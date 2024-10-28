/// This module defines a way to extend externally the CLI of hax, via
/// the `Extension` trait. This trait defines one associated type per
/// extension point.
use crate::prelude::*;

use clap::{Parser, Subcommand};

macro_rules! trait_alias {
    ($name:ident = $($base:tt)+) => {
        pub trait $name: $($base)+ { }
        impl<T: $($base)+> $name for T { }
    };
}

trait_alias!(
    ExtensionPoint =
        std::fmt::Debug
        + for<'a> serde::Deserialize<'a>
        + serde::Serialize
        + JsonSchema
        + Clone
);

trait_alias!(SubcommandExtensionPoint = ExtensionPoint + clap::Subcommand);
trait_alias!(ArgsExtensionPoint = ExtensionPoint + clap::Args);

#[derive_group(Serializers)]
#[derive(JsonSchema, Parser, Debug, Clone)]
pub struct EmptyArgsExtension {}

#[derive_group(Serializers)]
#[derive(JsonSchema, Subcommand, Debug, Clone)]
pub enum EmptySubcommandExtension {}

pub trait Extension {
    type Options: ArgsExtensionPoint;
    type Command: SubcommandExtensionPoint;
    type BackendOptions: ArgsExtensionPoint;
    type FStarOptions: ArgsExtensionPoint;
}

impl Extension for () {
    type Options = EmptyArgsExtension;
    type Command = EmptySubcommandExtension;
    type BackendOptions = EmptyArgsExtension;
    type FStarOptions = EmptyArgsExtension;
}
