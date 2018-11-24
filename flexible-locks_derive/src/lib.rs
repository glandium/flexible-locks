// Copyright 2018 Mike Hommey
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![recursion_limit = "128"]

extern crate proc_macro;
extern crate syn;

#[macro_use]
extern crate quote;

use proc_macro::TokenStream;
use quote::ToTokens;
use std::ops::Deref;
use syn::{Data, DeriveInput, Field, Fields, Index, Meta};

enum StructField<'a> {
    Numbered(Index, &'a Field),
    Named(&'a Field),
}

impl<'a> From<(usize, &'a Field)> for StructField<'a> {
    fn from((n, f): (usize, &'a Field)) -> Self {
        match f.ident {
            Some(_) => StructField::Named(f),
            None => StructField::Numbered(n.into(), f),
        }
    }
}

impl<'a> Deref for StructField<'a> {
    type Target = Field;
    fn deref(&self) -> &Field {
        match self {
            &StructField::Numbered(_, ref f) => f,
            &StructField::Named(ref f) => f,
        }
    }
}

impl<'a> StructField<'a> {
    fn quote_with_self(&self) -> impl ToTokens {
    match self {
        &StructField::Numbered(ref n, _) => quote! { self.#n },
        &StructField::Named(&Field {
            ident: Some(ref i), ..
        }) => quote! { self.#i },
        _ => unreachable!(),
    }
    }
}

#[proc_macro_derive(MutexProtected, attributes(mutex))]
pub fn derive_zero(input: TokenStream) -> TokenStream {
    let input: DeriveInput = syn::parse(input).unwrap();

    let name = input.ident;

    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    let mut types = vec![];

    match input.data {
        Data::Struct(ref data) => match data.fields {
            Fields::Named(ref fields) => types.extend(&fields.named),
            Fields::Unnamed(ref fields) => types.extend(&fields.unnamed),
            Fields::Unit => {}
        },
        _ => panic!("Can only derive(MutexProtected) for structs"),
    }

    let (mut mutexes, others): (Vec<_>, Vec<_>) = types
        .into_iter()
        .enumerate()
        .map(StructField::from)
        .partition(|f| {
            f.attrs.iter().any(|a| match a.interpret_meta() {
                Some(Meta::Word(ref id)) if id == "mutex" => true,
                Some(ref meta) if meta.name() == "mutex" => panic!("Expected #[mutex]"),
                _ => false,
            })
        });

    let mutex = match mutexes.len() {
        0 => panic!("Missing #[mutex]"),
        1 => mutexes.pop().unwrap(),
        _ => panic!("Can only have one #[mutex]"),
    };
    let mutex_ty = &mutex.ty;
    let mutex = mutex.quote_with_self();

    let (data_ty, data, data_mut, into_data) = match others.len() {
        0 => panic!("{} contains nothing else than a #[mutex] field", name),
        1 => {
            let other = &others[0];
            let other_ty = &other.ty;
            let data_ty = quote! { #other_ty };
            let qualified = other.quote_with_self();
            let data = quote! { &#qualified };
            let data_mut = quote! { &mut #qualified };
            let into_data = quote! { #qualified };
            (data_ty, data, data_mut, into_data)
        }
        _ => {
            let data_ty = quote! { #name #ty_generics };
            let data = quote! { self };
            let data_mut = data.clone();
            let into_data = data.clone();
            (data_ty, data, data_mut, into_data)
        }
    };

    let expanded = quote!{
        impl #impl_generics ::flexible_locks::MutexProtected for #name #ty_generics #where_clause {
            type MutexType = #mutex_ty;
            type DataType = #data_ty;
            fn get_mutex(&self) -> &Self::MutexType {
                &#mutex
            }
            fn get_mutex_mut(&mut self) -> &mut Self::MutexType {
                &mut #mutex
            }
            fn get_data(&self) -> &Self::DataType {
                #data
            }
            fn get_data_mut(&mut self) -> &mut Self::DataType {
                #data_mut
            }
            fn into_data(self) -> Self::DataType where Self::DataType: Sized {
                unsafe { self.get_mutex().destroy(); }
                #into_data
            }
        }
    };
    expanded.into()
}
