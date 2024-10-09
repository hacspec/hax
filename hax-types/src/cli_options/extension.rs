/// This module defines a way to extend externally the CLI of hax, via
/// the `Extension` trait. This trait defines one associated type per
/// extension point.
use crate::prelude::*;

use clap::{Parser, Subcommand};

macro_rules! mk_Extension_trait {
    {$(type $name:ident : $kind:ident;)+} => {
        pub trait Extension {
            $(type $name: bincode::Decode
              + bincode::Encode
              + std::fmt::Debug
              + for<'a> serde::Deserialize<'a>
              + serde::Serialize
              + JsonSchema
              + Clone
              + for<'a> bincode::BorrowDecode<'a>
              + clap::$kind;)+
        }

        /// `()` is the empty extension
        const _: () = {
            use NoExtensionStruct as Args;
            use NoExtensionEnum as Subcommand;

            impl Extension for () {
                $(type $name = $kind;)+
            }
        };

    };
}

#[derive_group(Serializers)]
#[derive(JsonSchema, Parser, Debug, Clone)]
pub struct NoExtensionStruct {}

#[derive_group(Serializers)]
#[derive(JsonSchema, Subcommand, Debug, Clone)]
pub enum NoExtensionEnum {}

mk_Extension_trait! {
    type Options: Args;
    type Command: Subcommand;
    type BackendOptions: Args;
    type FStarOptions: Args;
}
