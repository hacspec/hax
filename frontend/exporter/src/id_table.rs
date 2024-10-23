/// This module provides a notion of table, identifiers and nodes. A
/// `Node<T>` is a `Arc<T>` bundled with a unique identifier such that
/// there exists an entry in a table for that identifier.
///
/// The type `WithTable<T>` bundles a table with a value of type
/// `T`. That value of type `T` may hold an arbitrary number of
/// `Node<_>`s. In the context of a `WithTable<T>`, the type `Node<_>`
/// serializes and deserializes using a table as a state. In this
/// case, serializing a `Node<U>` produces only an identifier, without
/// any data of type `U`. Deserializing a `Node<U>` under a
/// `WithTable<T>` will recover `U` data from the table held by
/// `WithTable`.
///
/// Serde is not designed for stateful (de)serialization. There is no
/// way of deriving `serde::de::DeserializeSeed` systematically. This
/// module thus makes use of global state to achieve serialization and
/// deserialization. This modules provides an API that hides this
/// global state.
use crate::prelude::*;
use std::{
    hash::{Hash, Hasher},
    sync::{atomic::Ordering, Arc, LazyLock, Mutex, MutexGuard},
};

/// Unique IDs in a ID table.
#[derive_group(Serializers)]
#[derive(Default, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[serde(transparent)]
pub struct Id {
    id: u32,
}

/// A session providing fresh IDs for ID table.
#[derive(Default, Debug)]
pub struct Session {
    next_id: Id,
    table: Table,
}

impl Session {
    pub fn table(&self) -> &Table {
        &self.table
    }
}

/// The different types of values one can store in an ID table.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub enum Value {
    Ty(Arc<TyKind>),
}

/// A node is a bundle of an ID with a value.
#[derive(Deserialize, Serialize, Debug, JsonSchema, PartialEq, Eq, PartialOrd, Ord)]
#[serde(into = "serde_repr::NodeRepr<T>")]
#[serde(try_from = "serde_repr::NodeRepr<T>")]
pub struct Node<T: 'static + SupportedType> {
    id: Id,
    value: Arc<T>,
}

/// Hax relies on hashes being deterministic for predicates
/// ids. Identifiers are not deterministic: we implement hash for
/// `Node` manually, discarding the field `id`.
impl<T: SupportedType + Hash> Hash for Node<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.value.as_ref().hash(state);
    }
}

/// Manual implementation of `Clone` that doesn't require a `Clone`
/// bound on `T`.
impl<T: SupportedType> Clone for Node<T> {
    fn clone(&self) -> Self {
        Self {
            id: self.id.clone(),
            value: self.value.clone(),
        }
    }
}

/// A table is a map from IDs to `Value`s. When serialized, we
/// represent a table as a *sorted* vector. Indeed, the values stored
/// in the table might reference each other, without cycle, so the
/// order matters.
#[derive(Default, Debug, Clone, Deserialize, Serialize)]
#[serde(into = "serde_repr::SortedIdValuePairs")]
#[serde(from = "serde_repr::SortedIdValuePairs")]
pub struct Table(HashMap<Id, Value>);

impl Table {
    pub(super) fn insert<T>(&mut self, cache_id: Id, value: Arc<T>)
    where
        T: SupportedType,
    {
        self.0.insert(cache_id, T::to_types(value));
    }
    pub(super) fn get<T>(&self, cache_id: &Id) -> Option<Option<Arc<T>>>
    where
        T: SupportedType,
    {
        self.0.get(cache_id).map(T::from_types)
    }
}
impl SupportedType for TyKind {
    fn to_types(value: Arc<Self>) -> Value {
        Value::Ty(value)
    }
    fn from_types(t: &Value) -> Option<Arc<Self>> {
        match t {
            Value::Ty(value) => Some(value.clone()),
        }
    }
}

/// A value encodable in the enum `Value`
pub trait SupportedType: std::fmt::Debug {
    fn to_types(value: Arc<Self>) -> Value;
    fn from_types(t: &Value) -> Option<Arc<Self>>;
}

impl Session {
    fn fresh_id(&mut self) -> Id {
        let id = self.next_id.id;
        self.next_id.id += 1;
        Id { id }
    }
}

impl<T: Sync + Send + Clone + 'static + SupportedType> Node<T> {
    pub fn new(value: T, session: &mut Session) -> Self {
        let id = session.fresh_id();
        let kind = Arc::new(value);
        session.table.insert(id.clone(), kind.clone());
        Self { id, value: kind }
    }
    pub fn inner(&self) -> &Arc<T> {
        &self.value
    }
}

/// Wrapper for a type `T` that creates a bundle containing both a ID
/// table and a value `T`. That value may contains `Node` values
/// inside it. Serializing `WithTable<T>` will serialize IDs only,
/// skipping values. Deserialization of a `WithTable<T>` will
/// automatically use the table and IDs to reconstruct skipped values.
#[derive(Serialize, Debug)]
pub struct WithTable<T> {
    table: Table,
    value: T,
}

/// The state used for deserialization: a table.
static DESERIALIZATION_STATE: LazyLock<Mutex<Table>> =
    LazyLock::new(|| Mutex::new(Table::default()));
static DESERIALIZATION_STATE_LOCK: LazyLock<Mutex<()>> = LazyLock::new(|| Mutex::new(()));

/// The mode of serialization: should `Node<T>` ship values of type `T` or not?
static SERIALIZATION_MODE_USE_IDS: std::sync::atomic::AtomicBool =
    std::sync::atomic::AtomicBool::new(false);

fn serialize_use_id() -> bool {
    SERIALIZATION_MODE_USE_IDS.load(Ordering::Relaxed)
}

impl<T> WithTable<T> {
    /// Runs `f` with a `WithTable<T>` created out of `map` and
    /// `value`. Any serialization of values of type `Node<_>` will
    /// skip the field `value`.
    pub fn run<R>(map: Table, value: T, f: impl FnOnce(&Self) -> R) -> R {
        if serialize_use_id() {
            panic!("CACHE_MAP_LOCK: only one WithTable serialization can occur at a time (nesting is forbidden)")
        }
        SERIALIZATION_MODE_USE_IDS.store(true, Ordering::Relaxed);
        let result = f(&Self { table: map, value });
        SERIALIZATION_MODE_USE_IDS.store(false, Ordering::Relaxed);
        result
    }
    pub fn destruct(self) -> (T, Table) {
        let Self { value, table: map } = self;
        (value, map)
    }
}

/// Helper function that makes sure no nested deserializations occur.
fn full_id_deserialization<T>(f: impl FnOnce() -> T) -> T {
    let _lock: MutexGuard<_> = DESERIALIZATION_STATE_LOCK.try_lock().expect("CACHE_MAP_LOCK: only one WithTable deserialization can occur at a time (nesting is forbidden)");
    let result = f();
    result
}

/// The deserializer of `WithTable<T>` is special. First, we need to continuously
impl<'de, T: Deserialize<'de>> serde::Deserialize<'de> for WithTable<T> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        use serde::de::{self, Deserialize, MapAccess, SeqAccess, Visitor};
        use std::fmt;
        use std::marker::PhantomData;
        #[derive(Deserialize, Debug)]
        #[serde(field_identifier, rename_all = "lowercase")]
        enum Field {
            Table,
            Value,
        }

        struct WithTableVisitor<T>(PhantomData<T>);

        impl<'de, T: Deserialize<'de>> Visitor<'de> for WithTableVisitor<T> {
            type Value = WithTable<T>;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("struct WithTable")
            }

            fn visit_seq<V>(self, mut seq: V) -> Result<Self::Value, V::Error>
            where
                V: SeqAccess<'de>,
            {
                let (table, value) =
                    full_id_deserialization::<Result<(Table, T), V::Error>>(|| {
                        let previous = std::mem::take(&mut *DESERIALIZATION_STATE.lock().unwrap());
                        // Deserializing `Node<T>`s populates `DESERIALIZATION_STATE`: the table
                        // is already constructed in `DESERIALIZATION_STATE`, we discard it below.
                        let _: Table = seq
                            .next_element()?
                            .ok_or_else(|| de::Error::invalid_length(0, &self))?;
                        let value = seq.next_element::<T>().and_then(|inner| {
                            inner.ok_or_else(|| de::Error::invalid_length(1, &self))
                        });
                        let table = std::mem::replace(
                            &mut *DESERIALIZATION_STATE.lock().unwrap(),
                            previous,
                        );
                        let value = value?;
                        Ok((table, value))
                    })?;
                Ok(Self::Value { table, value })
            }

            fn visit_map<V>(self, mut map: V) -> Result<Self::Value, V::Error>
            where
                V: MapAccess<'de>,
            {
                let (table, value) = full_id_deserialization::<Result<(Table, T), V::Error>>(
                    || {
                        let (table_key, table): (Field, Table) = map
                            .next_entry()?
                            .ok_or(de::Error::custom("Expected field `table` *first*"))?;
                        if !matches!(table_key, Field::Table) {
                            Err(de::Error::custom("Expected field `table` *first*"))?
                        }
                        let previous =
                            std::mem::replace(&mut *DESERIALIZATION_STATE.lock().unwrap(), table);

                        let value_result = map.next_entry::<Field, T>().and_then(|inner| {
                            inner.ok_or_else(|| {
                                de::Error::custom("Expected field `value`, got something else? Seems like the type is wrong.")
                            })
                        });
                        let table = std::mem::replace(
                            &mut *DESERIALIZATION_STATE.lock().unwrap(),
                            previous,
                        );
                        let (value_key, value) = value_result?;
                        if !matches!(value_key, Field::Value) {
                            Err(de::Error::custom(&format!(
                                "Expected field `value`, found {:#?}",
                                value_key
                            )))?
                        }
                        if let Some(field) = map.next_key()? {
                            Err(de::Error::unknown_field(field, &["nothing left"]))?
                        }
                        Ok((table, value))
                    },
                )?;
                Ok(Self::Value { table, value })
            }
        }

        const FIELDS: &[&str] = &["table", "value"];
        let r = deserializer.deserialize_struct("WithTable", FIELDS, WithTableVisitor(PhantomData));
        r
    }
}

/// Defines representations for various types when serializing or/and
/// deserializing via serde
mod serde_repr {
    use super::*;

    #[derive(Serialize, Deserialize, JsonSchema, Debug)]
    pub(super) struct NodeRepr<T> {
        cache_id: Id,
        value: Option<Arc<T>>,
    }

    #[derive(Serialize)]
    pub(super) struct Pair(Id, Value);
    pub(super) type SortedIdValuePairs = Vec<Pair>;

    impl<T: SupportedType> Into<NodeRepr<T>> for Node<T> {
        fn into(self) -> NodeRepr<T> {
            let value = if serialize_use_id() {
                None
            } else {
                Some(self.value.clone())
            };
            let cache_id = self.id;
            NodeRepr { value, cache_id }
        }
    }

    impl<T: 'static + SupportedType> TryFrom<NodeRepr<T>> for Node<T> {
        type Error = serde::de::value::Error;

        fn try_from(cached: NodeRepr<T>) -> Result<Self, Self::Error> {
            use serde::de::Error;
            let map = DESERIALIZATION_STATE.lock().unwrap();
            let id = cached.cache_id;
            let kind = if let Some(kind) = cached.value {
                kind
            } else {
                map.get(&id)
                    .ok_or_else(|| {
                        Self::Error::custom(&format!(
                            "Stateful deserialization failed for id {:?}: not found in cache",
                            id
                        ))
                    })?
                    .ok_or_else(|| {
                        Self::Error::custom(&format!(
                            "Stateful deserialization failed for id {:?}: wrong type",
                            id
                        ))
                    })?
            };
            Ok(Self { value: kind, id })
        }
    }

    impl<'de> serde::Deserialize<'de> for Pair {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: serde::Deserializer<'de>,
        {
            let (id, v) = <(Id, Value)>::deserialize(deserializer)?;
            DESERIALIZATION_STATE
                .lock()
                .unwrap()
                .0
                .insert(id.clone(), v.clone());
            Ok(Pair(id, v))
        }
    }

    impl Into<SortedIdValuePairs> for Table {
        fn into(self) -> SortedIdValuePairs {
            let mut vec: Vec<_> = self.0.into_iter().map(|(x, y)| Pair(x, y)).collect();
            vec.sort_by_key(|o| o.0.clone());
            vec
        }
    }

    impl From<SortedIdValuePairs> for Table {
        fn from(t: SortedIdValuePairs) -> Self {
            Self(HashMap::from_iter(t.into_iter().map(|Pair(x, y)| (x, y))))
        }
    }
}
