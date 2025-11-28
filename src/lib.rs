//! Crepe is a library that allows you to write declarative logic programs in
//! Rust, with a [Datalog](https://en.wikipedia.org/wiki/Datalog)-like syntax.
//! It provides a procedural macro that generates efficient, safe code and
//! interoperates seamlessly with Rust programs.
//!
//! # Documentation
//! See the [`crepe!`](macro.crepe.html) macro for detailed documentation.

#![forbid(unsafe_code)]
#![deny(missing_docs)]

extern crate proc_macro;

mod parse;
mod strata;

use proc_macro::TokenStream;
use proc_macro_error::{abort, emit_error, proc_macro_error};
use quote::{format_ident, quote, quote_spanned};
use std::collections::{HashMap, HashSet};
use std::fmt::{self, Display, Formatter};
use syn::{parse_macro_input, spanned::Spanned, Expr, Ident, Lifetime, Pat, Type};

use parse::{Clause, Fact, FactField, For, Program, Relation, RelationType, Rule};
use strata::Strata;

/// The main macro, which lets you write a Datalog program declaratively.
///
/// # Example
/// A program to calculate transitive closure might be written as:
/// ```
/// mod datalog {
///     use crepe::crepe;
///
///     crepe! {
///         @input
///         struct Edge(i32, i32);
///
///         @output
///         struct Tc(i32, i32);
///
///         Tc(x, y) <- Edge(x, y);
///         Tc(x, z) <- Edge(x, y), Tc(y, z);
///     }
///
///     pub fn run(edges: &[(i32, i32)]) -> Vec<(i32, i32)> {
///         let mut runtime = Crepe::new();
///         runtime.extend(edges.iter().map(|&(a, b)| Edge(a, b)));
///         let (tc,) = runtime.run();
///         tc.into_iter().map(|Tc(a, b)| (a, b)).collect()
///     }
/// }
/// # fn main() {}
/// ```
///
/// # Generated Code
/// Each `struct` in the program is turned into a Datalog relation, while each
/// line of the form `goal <- clause1, clause2, ...;` or `fact;` defines a
/// logic programming rule that is used to derive new relations.
///
/// In addition to the relation structs, the macro also defines a `Crepe`
/// struct representing the runtime. This is the primary way that you interact
/// with Crepe. It provides a couple methods and traits (here `Rel` is a
/// placeholder for the name of your relation):
///
/// - `Crepe::new()`: construct a new runtime
/// - Implements `std::iter::Extend<Rel>` for each @input struct.
///   - `Crepe::extend(&mut self, iter: impl IntoIterator<Item = Rel>)`
/// - Implements `std::iter::Extend<&'a Rel>` for each @input struct.
///   - `Crepe::extend(&mut self, iter: impl IntoIterator<Item = &'a Rel>)`
/// - `Crepe::run(self)`: evaluates the Datalog program on the given inputs,
///   consuming the runtime object, and returns a tuple of `HashSet<Rel>`s
///   containing the final derived @output structs.
/// - `Crepe::run_with_hasher::<S: BuildHasher + Default>(self)`: similar to the
///   `run` method, but internally uses a custom hasher.
/// - `Crepe::run_with_provenance(self)`: evaluates the Datalog program and
///   returns both the output relations and a `Provenance` object that tracks
///   which rules and facts led to each derived fact.
/// - `Crepe::run_with_provenance_and_hasher::<S: BuildHasher + Default>(self)`:
///   similar to `run_with_provenance`, but uses a custom hasher.
///
/// In order for the engine to work, all relations must be tuple structs, and
/// they automatically derive the `Eq`, `PartialEq`, `Hash`, `Copy`, and
/// `Clone` traits. This is necessary in order to create efficient indices that
/// are used in Datalog evaluation. If you want to use Crepe with types that
/// do not implement `Copy`, consider passing references instead.
///
/// # Datalog Syntax Extensions
/// This library supports arbitrary Rust expression syntax within rules for
/// constructing new relations, as well as Boolean expressions that are
/// evaluated directly as clauses in rules. Basically, this gives you seamless
/// Rust interoperability within your Datalog programs.
///
/// For instance, here is a program that calculates the first 25 Fibonacci
/// numbers using arithmetic functors:
/// ```
/// # mod datalog {
/// #     use crepe::crepe;
/// crepe! {
///     @output
///     struct Fib(u32, u32);
///
///     Fib(0, 0) <- (true);
///     Fib(1, 1); // shorthand for `Fib(1, 1) <- (true);`
///
///     Fib(n + 2, x + y) <- Fib(n, x), Fib(n + 1, y), (n + 2 <= 25);
/// }
/// #     pub fn run() -> Vec<(u32, u32)> {
/// #         let (fib,) = Crepe::new().run();
/// #         let mut output: Vec<_> = fib.into_iter().map(|Fib(x, y)| (x, y)).collect();
/// #         output.sort();
/// #         output
/// #     }
/// # }
/// #
/// # fn main() {
/// #     let results = datalog::run();
/// #     assert_eq!(
/// #         results,
/// #         [
/// #             (0, 0),
/// #             (1, 1),
/// #             (2, 1),
/// #             (3, 2),
/// #             (4, 3),
/// #             (5, 5),
/// #             (6, 8),
/// #             (7, 13),
/// #             (8, 21),
/// #             (9, 34),
/// #             (10, 55),
/// #             (11, 89),
/// #             (12, 144),
/// #             (13, 233),
/// #             (14, 377),
/// #             (15, 610),
/// #             (16, 987),
/// #             (17, 1597),
/// #             (18, 2584),
/// #             (19, 4181),
/// #             (20, 6765),
/// #             (21, 10946),
/// #             (22, 17711),
/// #             (23, 28657),
/// #             (24, 46368),
/// #             (25, 75025)
/// #         ]
/// #     );
/// # }
/// ```
/// Note that all Boolean conditions within the clauses of rules are evaluated
/// in-place, and they must be surrounded by parentheses.
///
/// We also support let-bindings in rules, including bindings that destructure
/// their arguments conditionally. See `tests/test_destructure.rs` for an
/// example of this.
/// ```
/// # use crepe::crepe;
/// crepe! {
///     @input
///     struct Value<'a>(&'a str);
///
///     @output
/// #   #[derive(Debug)]
///     struct Squared(i32, i32);
///
///     Squared(n, x) <-
///         Value(string),
///         let Ok(n) = string.parse(),
///         let x = n * n;
/// }
/// # fn main() {
/// #     let mut rt = Crepe::new();
/// #     rt.extend([Value("hello"), Value("42")]);
/// #     let (squared,) = rt.run();
/// #     assert_eq!(squared.into_iter().collect::<Vec<_>>(), [Squared(42, 1764)]);
/// # }
/// ```
/// The last built-in control flow feature is iteration over data. Rules can
/// enumerate values from an iterator, allowing them to use data from outside of
/// Crepe without having to convert functions to use work-arounds. For example,
/// to access the characters of a string, you could write:
/// ```
/// # use crepe::crepe;
/// crepe! {
///     @input
///     struct Name<'a>(&'a str);
///
///     @output
///     struct NameContainsLetter<'a>(&'a str, char);
///
///     NameContainsLetter(name, letter) <- Name(name), for letter in name.chars();
/// }
/// ```
///
/// # Evaluation Mode
/// All generated code uses semi-naive evaluation (see Chapter 3 of _Datalog
/// and Recursive Query Processing_), and it is split into multiple strata to
/// enable stratified negation. For example, we can extend the first example to
/// also compute the complement of transitive closure in a graph:
/// ```
/// mod datalog {
///     use crepe::crepe;
///
///     crepe! {
///         @input
///         struct Edge(i32, i32);
///
///         @output
///         struct Tc(i32, i32);
///
///         struct Node(i32);
///
///         @output
///         struct NotTc(i32, i32);
///
///         Tc(x, y) <- Edge(x, y);
///         Tc(x, z) <- Edge(x, y), Tc(y, z);
///
///         Node(x) <- Edge(x, _);
///         Node(x) <- Edge(_, x);
///         NotTc(x, y) <- Node(x), Node(y), !Tc(x, y);
///     }
///
///     pub fn run(edges: &[(i32, i32)]) -> (Vec<(i32, i32)>, Vec<(i32, i32)>) {
///         let mut runtime = Crepe::new();
///         runtime.extend(edges.iter().map(|&(a, b)| Edge(a, b)));
///         let (tc, not_tc) = runtime.run();
///         (
///             tc.into_iter().map(|Tc(a, b)| (a, b)).collect(),
///             not_tc.into_iter().map(|NotTc(a, b)| (a, b)).collect(),
///         )
///     }
/// }
/// # fn main() {}
/// ```
///
/// # Lifetimes and Attributes
/// This macro allows you to specify attributes, visibility modifiers, and
/// lifetimes on the relation structs. These can include additional `derive`
/// attributes, and lifetimes can be used to construct relations that include
/// non-owning references. The following example computes suffixes of words.
/// ```
/// use crepe::crepe;
///
/// crepe! {
///     @input
///     struct Word<'a>(&'a str);
///
///     @output
///     #[derive(Debug)]
///     struct Suffix<'a>(&'a str);
///
///     Suffix(w) <- Word(w);
///     Suffix(&w[1..]) <- Suffix(w), (!w.is_empty());
/// }
///
/// fn main() {
///     let mut runtime = Crepe::new();
///     runtime.extend([Word("banana"), Word("bandana")]);
///     let (suffixes,) = runtime.run();
///     println!("{:?}", suffixes);
/// }
/// ```
/// We also support the `ref` keyword for binding a variable by reference rather
/// than copying it, which can improve performance in some cases.
///
/// # Hygiene
/// In addition to the relation structs, this macro generates implementations
/// of a private struct named `Crepe` for the runtime. Therefore, it is
/// recommended to place each Datalog program within its own module, to prevent
/// name collisions.
#[proc_macro]
#[proc_macro_error]
pub fn crepe(input: TokenStream) -> TokenStream {
    let program = parse_macro_input!(input as Program);
    let context = Context::new(program);

    let struct_decls = make_struct_decls(&context);
    let runtime_decl = make_runtime_decl(&context);
    let runtime_impl = make_runtime_impl(&context);

    let expanded = quote! {
        #struct_decls
        #runtime_decl
        #runtime_impl
    };

    expanded.into()
}

/// Function that takes a `TokenStream` as input, and returns a `TokenStream`
type QuoteWrapper = dyn Fn(proc_macro2::TokenStream) -> proc_macro2::TokenStream;

/// Intermediate representation for Datalog compilation
struct Context {
    has_input_lifetime: bool,
    rels_input: HashMap<String, Relation>,
    rels_output: HashMap<String, Relation>,
    output_order: Vec<Ident>,
    rels_intermediate: HashMap<String, Relation>,
    rules: Vec<Rule>,
    strata: Strata,
}

impl Context {
    fn new(program: Program) -> Self {
        // Read in relations, ensure no duplicates
        let mut rels_input = HashMap::new();
        let mut rels_output = HashMap::new();
        let mut rels_intermediate = HashMap::new();
        let mut rel_names = HashSet::new();
        let mut output_order = Vec::new();

        let mut has_input_lifetime = false;
        let mut has_output_lifetime = false;

        program.relations.into_iter().for_each(|relation| {
            let name = relation.name.to_string();
            if !rel_names.insert(relation.name.clone()) {
                abort!(relation.name.span(), "Duplicate relation name: {}", name);
            }

            // Validate generic parameters
            validate_generic_params(&relation);
            
            let num_lifetimes = relation.generics.lifetimes().count();

            match relation.relation_type() {
                Ok(RelationType::Input) => {
                    rels_input.insert(name, relation);
                    if num_lifetimes > 0 {
                        has_input_lifetime = true;
                    }
                }
                Ok(RelationType::Output) => {
                    output_order.push(relation.name.clone());
                    rels_output.insert(name, relation);
                    if num_lifetimes > 0 {
                        has_output_lifetime = true;
                    }
                }
                Ok(RelationType::Intermediate) => {
                    rels_intermediate.insert(name, relation);
                }
                Err(attr) => {
                    abort!(
                        attr.span(),
                        "Invalid attribute @{}, expected '@input' or '@output'",
                        attr
                    )
                }
            }
        });

        // all lifetimes currently are set to the input lifetime, so one needs to
        // be present somewhere
        if has_output_lifetime && !has_input_lifetime {
            // This should be the exception (assuming most crepe programs are
            // well "lifetimed") so for all structs that have lifetimes but
            // should not have one, an error gets emitted

            for r in rels_output.values() {
                if r.generics.lifetimes().next().is_some() {
                    emit_error!(
                        r.generics,
                        "Lifetime on output relation without any input relations having a lifetime"
                    );
                }
            }
        }

        // Read in rules, ensuring that there are no undefined relations, or
        // relations declared with incorrect arity.
        //
        // Also generate dependency edges between relations for stratification.
        let mut dependencies = HashSet::new();
        let check = |fact: &Fact| {
            let name = fact.relation.to_string();
            if !rel_names.contains(&fact.relation) {
                abort!(
                    fact.relation.span(),
                    "Relation name '{}' was not found. Did you misspell it?",
                    name
                );
            }
            let rel = rels_input
                .get(&name)
                .or_else(|| rels_output.get(&name))
                .or_else(|| rels_intermediate.get(&name))
                .expect("relation should exist");
            if rel.fields.len() != fact.fields.len() {
                abort!(
                    fact.relation.span(),
                    "Relation '{}' was declared with arity {}, but constructed with arity {} here.",
                    name,
                    rel.fields.len(),
                    fact.fields.len(),
                );
            }
        };
        program.rules.iter().for_each(|rule| {
            check(&rule.goal);
            if rels_input.get(&rule.goal.relation.to_string()).is_some() {
                abort!(
                    rule.goal.relation.span(),
                    "Relations marked as @input cannot be derived from a rule."
                )
            }

            for f in &rule.goal.fields {
                match f {
                    FactField::Ignored(token) => {
                        abort!(token.span(), "Cannot have _ in goal atom of rule.")
                    }
                    FactField::Ref(token, _) => {
                        abort!(token.span(), "Cannot have `ref` in goal atom of rule.")
                    }
                    FactField::Expr(_) => (),
                }
            }
            rule.clauses.iter().for_each(|clause| {
                if let Clause::Fact(fact) = clause {
                    check(fact);
                    dependencies.insert((&rule.goal.relation, &fact.relation));
                }
            });
        });

        // Now we can stratify the relations
        let strata = Strata::new(rel_names, dependencies);

        // Check for dependency cycles in datalog negations
        for rule in &program.rules {
            let goal_stratum = strata.find_relation(&rule.goal.relation);
            for clause in &rule.clauses {
                if let Clause::Fact(fact) = clause {
                    if fact.negate.is_some() {
                        let fact_stratum = strata.find_relation(&fact.relation);
                        if goal_stratum == fact_stratum {
                            abort!(
                                fact.relation.span(),
                                "Negation of relation '{}' creates a dependency cycle \
                                and cannot be stratified.",
                                fact.relation
                            );
                        }
                        // This should be guaranteed by reverse topological order
                        assert!(goal_stratum > fact_stratum);
                    }
                }
            }
        }

        // If all the relations are OK, we simply update the rules as-is.
        //
        // There's no need to do complex parsing logic yet; we can work that
        // out when we actually generate the runtime code, since that's
        // context-sensitive logic.
        let rules = program.rules;
        Self {
            has_input_lifetime,
            rels_input,
            rels_output,
            output_order,
            rels_intermediate,
            rules,
            strata,
        }
    }

    fn get_relation(&self, name: &str) -> Option<&Relation> {
        self.rels_input
            .get(name)
            .or_else(|| self.rels_intermediate.get(name))
            .or_else(|| self.rels_output.get(name))
    }

    fn all_relations(&self) -> impl Iterator<Item = &Relation> {
        self.rels_input
            .values()
            .chain(self.rels_intermediate.values())
            .chain(self.rels_output.values())
    }
}

#[derive(Eq, PartialEq, Hash, Copy, Clone)]
enum IndexMode {
    Bound,
    Free,
}

#[derive(Eq, PartialEq, Hash, Clone)]
struct Index {
    name: Ident,
    mode: Vec<IndexMode>,
}

impl Index {
    fn to_ident(&self) -> Ident {
        Ident::new(&self.to_string(), self.name.span())
    }

    fn key_type<'a>(&self, context: &'a Context) -> Vec<&'a Type> {
        let rel = context
            .get_relation(&self.name.to_string())
            .expect("could not find relation of index name");
        self.mode
            .iter()
            .zip(rel.fields.iter())
            .filter_map(|(mode, field)| match mode {
                IndexMode::Bound => Some(&field.ty),
                IndexMode::Free => None,
            })
            .collect()
    }

    fn bound_pos(&self) -> Vec<syn::Index> {
        self.mode
            .iter()
            .enumerate()
            .filter_map(|(i, mode)| match mode {
                IndexMode::Bound => Some(syn::Index::from(i)),
                IndexMode::Free => None,
            })
            .collect()
    }
}

impl Display for Index {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mode: String = self
            .mode
            .iter()
            .map(|mode| match mode {
                IndexMode::Bound => 'b',
                IndexMode::Free => 'f',
            })
            .collect();
        write!(f, "__{}_index{}", to_lowercase(&self.name), mode)
    }
}

fn make_struct_decls(context: &Context) -> proc_macro2::TokenStream {
    let relation_decls = context
        .all_relations()
        .map(|relation| {
            let attrs = &relation.attrs;
            let struct_token = &relation.struct_token;
            let vis = &relation.visibility;
            let name = &relation.name;
            let generics = &relation.generics;
            let semi_token = &relation.semi_token;
            let fields = &relation.fields;

            quote_spanned! {name.span()=>
                #[derive(
                    ::core::marker::Copy,
                    ::core::clone::Clone,
                    ::core::cmp::Eq,
                    ::core::cmp::PartialEq,
                    ::core::hash::Hash,
                )]
                #(#attrs)*
                #vis #struct_token #name #generics (#fields)#semi_token
            }
        });
    
    // Add provenance tracking structures
    let provenance_decls = quote! {
        /// Tracks how facts were derived during Datalog evaluation
        /// Uses ID-based tracking: each fact gets a unique ID
        #[derive(Debug, Clone, Default)]
        pub struct Provenance {
            /// Maps rule IDs to their descriptions
            rule_descriptions: ::std::collections::HashMap<usize, String>,
            /// Per-rule storage: Vec<(output_fact_id, vec_of_input_fact_ids)>
            /// Stored as a HashMap<rule_id, Vec<RuleApplication>>
            rule_applications: ::std::collections::HashMap<usize, ::std::vec::Vec<(usize, ::std::vec::Vec<usize>)>>,
        }
        
        impl Provenance {
            fn new() -> Self {
                Self::default()
            }
            
            /// Register a rule description
            fn register_rule(&mut self, rule_id: usize, description: String) {
                self.rule_descriptions.insert(rule_id, description);
                self.rule_applications.insert(rule_id, ::std::vec::Vec::new());
            }
            
            /// Add a rule application: which output fact ID was derived from which input fact IDs
            fn add_rule_application(&mut self, rule_id: usize, output_id: usize, input_ids: ::std::vec::Vec<usize>) {
                self.rule_applications
                    .entry(rule_id)
                    .or_insert_with(::std::vec::Vec::new)
                    .push((output_id, input_ids));
            }
            
            /// Get the description for a rule
            pub fn get_rule_description(&self, rule_id: usize) -> Option<&str> {
                self.rule_descriptions.get(&rule_id).map(|s| s.as_str())
            }
            
            /// Get all rule descriptions
            pub fn all_rule_descriptions(&self) -> Vec<(usize, &str)> {
                let mut result: Vec<_> = self.rule_descriptions
                    .iter()
                    .map(|(&id, desc)| (id, desc.as_str()))
                    .collect();
                result.sort_by_key(|(id, _)| *id);
                result
            }
            
            /// Get all applications of a specific rule
            pub fn rule_applications(&self, rule_id: usize) -> &[(usize, ::std::vec::Vec<usize>)] {
                self.rule_applications
                    .get(&rule_id)
                    .map(|v| v.as_slice())
                    .unwrap_or(&[])
            }
            
            /// Get derivation count for a specific rule
            pub fn rule_derivation_count(&self, rule_id: usize) -> usize {
                self.rule_applications
                    .get(&rule_id)
                    .map(|v| v.len())
                    .unwrap_or(0)
            }
            
            /// Get total number of derivations
            pub fn derivation_count(&self) -> usize {
                self.rule_applications.values().map(|v| v.len()).sum()
            }
            
            /// Reconstruct the derivation tree for a given fact ID
            /// Returns all fact IDs involved in deriving this fact (including the fact itself)
            pub fn explain(&self, fact_id: usize) -> ::std::vec::Vec<usize> {
                let mut result = ::std::vec::Vec::new();
                let mut visited = ::std::collections::HashSet::new();
                let mut stack = vec![fact_id];
                
                while let Some(current_id) = stack.pop() {
                    if !visited.insert(current_id) {
                        continue;
                    }
                    result.push(current_id);
                    
                    // Find which rule(s) derived this fact
                    for (_rule_id, applications) in &self.rule_applications {
                        for (output_id, input_ids) in applications {
                            if *output_id == current_id {
                                // This rule derived our fact, add its inputs to explore
                                for &input_id in input_ids {
                                    if !visited.contains(&input_id) {
                                        stack.push(input_id);
                                    }
                                }
                            }
                        }
                    }
                }
                
                result
            }
            
            /// Filter provenance to only include facts needed to derive the given output fact IDs
            /// Returns a new Provenance with only the relevant rule applications
            pub fn filter_for_outputs(&self, output_ids: &[usize]) -> Self {
                // Collect all fact IDs needed for these outputs
                let mut needed_facts = ::std::collections::HashSet::new();
                for &output_id in output_ids {
                    for fact_id in self.explain(output_id) {
                        needed_facts.insert(fact_id);
                    }
                }
                
                // Filter rule applications to only keep those that produce needed facts
                let mut filtered_applications = ::std::collections::HashMap::new();
                
                for (&rule_id, applications) in &self.rule_applications {
                    let mut filtered_apps = ::std::vec::Vec::new();
                    
                    for (output_id, input_ids) in applications {
                        if needed_facts.contains(output_id) {
                            // Only keep this application if its output is needed
                            filtered_apps.push((*output_id, input_ids.clone()));
                        }
                    }
                    
                    if !filtered_apps.is_empty() {
                        filtered_applications.insert(rule_id, filtered_apps);
                    }
                }
                
                Self {
                    rule_descriptions: self.rule_descriptions.clone(),
                    rule_applications: filtered_applications,
                }
            }
            
            /// Get all fact IDs that are "leaf" outputs (not used as inputs to any other derivation)
            /// These are typically the final results you care about
            pub fn get_output_fact_ids(&self) -> ::std::vec::Vec<usize> {
                let mut all_outputs = ::std::collections::HashSet::new();
                let mut all_inputs = ::std::collections::HashSet::new();
                
                for applications in self.rule_applications.values() {
                    for (output_id, input_ids) in applications {
                        all_outputs.insert(*output_id);
                        for &input_id in input_ids {
                            all_inputs.insert(input_id);
                        }
                    }
                }
                
                // Leaf outputs are those that are never used as inputs
                all_outputs.difference(&all_inputs).copied().collect()
            }
            
            /// Get all fact IDs (both inputs and derived facts)
            pub fn get_all_fact_ids(&self) -> ::std::vec::Vec<usize> {
                let mut all_facts = ::std::collections::HashSet::new();
                
                for applications in self.rule_applications.values() {
                    for (output_id, input_ids) in applications {
                        all_facts.insert(*output_id);
                        for &input_id in input_ids {
                            all_facts.insert(input_id);
                        }
                    }
                }
                
                let mut result: ::std::vec::Vec<_> = all_facts.into_iter().collect();
                result.sort();
                result
            }
            
            /// Pretty-print the provenance summary
            pub fn display(&self) -> String {
                let mut output = String::from("Provenance Summary:\n");
                output.push_str(&format!("\nTotal derivations: {}\n", self.derivation_count()));
                
                output.push_str("\nRules:\n");
                for (rule_id, desc) in self.all_rule_descriptions() {
                    let count = self.rule_derivation_count(rule_id);
                    output.push_str(&format!("  Rule {} (fired {} times): {}\n", rule_id, count, desc));
                }
                
                output.push_str("\nRule Applications:\n");
                for (rule_id, desc) in self.all_rule_descriptions() {
                    let apps = self.rule_applications(rule_id);
                    if !apps.is_empty() {
                        output.push_str(&format!("  Rule {}: {}\n", rule_id, desc));
                        for (output_id, input_ids) in apps {
                            output.push_str(&format!("    Fact #{} <- [{}]\n", 
                                output_id,
                                input_ids.iter().map(|id| format!("#{}", id)).collect::<Vec<_>>().join(", ")));
                        }
                    }
                }
                
                output
            }
            
            /// Output provenance in compact format
            /// Format: one line per fact ID (sorted)
            /// - Input facts: just the fact ID
            /// - Derived facts: fact_id rule_id input_id1 input_id2 ...
            pub fn display_compact(&self) -> String {
                let mut output = String::new();
                
                // Build a map of fact_id -> (rule_id, input_ids)
                let mut fact_derivations: ::std::collections::BTreeMap<usize, (usize, Vec<usize>)> = 
                    ::std::collections::BTreeMap::new();
                    
                for (&rule_id, apps) in &self.rule_applications {
                    for (output_id, input_ids) in apps {
                        fact_derivations.insert(*output_id, (rule_id, input_ids.clone()));
                    }
                }
                
                // Collect all fact IDs that appear in this provenance (after filtering)
                let mut all_fact_ids = ::std::collections::BTreeSet::new();
                
                for (output_id, input_ids) in fact_derivations.values() {
                    all_fact_ids.insert(*output_id);
                    for &input_id in input_ids {
                        all_fact_ids.insert(input_id);
                    }
                }
                
                // Output in compact format (sorted by fact ID)
                for fact_id in all_fact_ids {
                    if let Some((rule_id, input_ids)) = fact_derivations.get(&fact_id) {
                        // Derived fact: fact_id rule_id input_id1 input_id2 ...
                        output.push_str(&format!("{} {}", fact_id, rule_id));
                        for input_id in input_ids {
                            output.push_str(&format!(" {}", input_id));
                        }
                        output.push('\n');
                    } else {
                        // Input fact: just the fact_id
                        output.push_str(&format!("{}\n", fact_id));
                    }
                }
                
                output
            }
        }
    };
    
    relation_decls
        .chain(std::iter::once(provenance_decls))
        .collect()
}

fn make_runtime_decl(context: &Context) -> proc_macro2::TokenStream {
    let fields: proc_macro2::TokenStream = context
        .rels_input
        .values()
        .map(|relation| {
            let rel_ty = relation_type(relation, LifetimeUsage::Item);
            let lowercase_name = to_lowercase(&relation.name);
            quote! {
                #lowercase_name: ::std::vec::Vec<#rel_ty>,
            }
        })
        .collect();

    let generics_decl = generic_params_decl(context);

    quote! {
        #[derive(::core::default::Default)]
        struct Crepe #generics_decl {
            #fields
        }
    }
}

fn make_runtime_impl(context: &Context) -> proc_macro2::TokenStream {
    let builders = make_extend(context);
    let run = make_run(context);

    let generics_decl = generic_params_decl(context);
    let generics_args = generic_params_args(context);

    quote! {
        impl #generics_decl Crepe #generics_args {
            fn new() -> Self {
                ::core::default::Default::default()
            }
            #run
        }
        #builders
    }
}

fn make_extend(context: &Context) -> proc_macro2::TokenStream {
    context
        .rels_input
        .values()
        .map(|relation| {
            let rel_ty = relation_type(relation, LifetimeUsage::Item);
            let generics_decl = generic_params_decl(context);
            let generics_args = generic_params_args(context);
            let lower = to_lowercase(&relation.name);
            
            // For the reference impl, we need to add the lifetime to the existing generics
            let ref_impl_generics = {
                let mut items = vec![quote! { 'a }];
                for tp in collect_generic_params(context) {
                    items.push(merge_bounds_with_required(tp));
                }
                format_generics(items)
            };
            
            quote! {
                impl #generics_decl ::core::iter::Extend<#rel_ty> for Crepe #generics_args {
                    fn extend<__I>(&mut self, iter: __I)
                    where
                        __I: ::core::iter::IntoIterator<Item = #rel_ty>,
                    {
                        self.#lower.extend(iter);
                    }
                }
                impl #ref_impl_generics ::core::iter::Extend<&'a #rel_ty> for Crepe #generics_args {
                    fn extend<__I>(&mut self, iter: __I)
                    where
                        __I: ::core::iter::IntoIterator<Item = &'a #rel_ty>,
                    {
                        self.extend(iter.into_iter().copied());
                    }
                }
            }
        })
        .collect()
}

/// This is the primary method, which consumes the builder. It should compile
/// declarative Datalog into imperative logic to generate facts, essentially
/// what we signed up for!
///
/// Here's an example of what might be generated for transitive closure:
/// ```ignore
/// fn run_with_hasher<CrepeHasher: BuildHasher + Default>(
///     self,
/// ) -> (::std::collections::HashSet<Tc, CrepeHasher>,) {
///     // Relations
///     let mut __edge: ::std::collections::HashSet<Edge, CrepeHasher> =
///         ::std::collections::HashSet::default();
///     let mut __edge_update: ::std::collections::HashSet<Edge, CrepeHasher> =
///         ::std::collections::HashSet::default();
///     let mut __tc: ::std::collections::HashSet<Tc, CrepeHasher> =
///         ::std::collections::HashSet::default();
///     let mut __tc_update: ::std::collections::HashSet<Tc, CrepeHasher> =
///         ::std::collections::HashSet::default();
///
///     // Indices
///     let mut __tc_index_bf: ::std::collections::HashMap<
///         (i32,),
///         ::std::vec::Vec<Tc>,
///         CrepeHasher,
///     > = ::std::collections::HashMap::default();
///
///     // Input relations
///     __edge_update.extend(self.edge);
///
///     // Main loop, single stratum for simplicity
///     let mut __crepe_first_iteration = true;
///     while __crepe_first_iteration || !(__edge_update.is_empty() && __tc_update.is_empty()) {
///         __tc.extend(&__tc_update);
///         for __crepe_var in &__tc_update {
///             __tc_index_bf
///                 .entry((__crepe_var.0,))
///                 .or_default()
///                 .push(*__crepe_var);
///         }
///         __edge.extend(&__edge_update);
///
///         let mut __tc_new: ::std::collections::HashSet<Tc, CrepeHasher> =
///             ::std::collections::HashSet::default();
///         let mut __edge_new: ::std::collections::HashSet<Edge, CrepeHasher> =
///             ::std::collections::HashSet::default();
///
///         for __crepe_var in &__edge {
///             let x = __crepe_var.0;
///             let y = __crepe_var.1;
///             let __crepe_goal = Tc(x, y);
///             if !__tc.contains(&__crepe_goal) {
///                 __tc_new.insert(__crepe_goal);
///             }
///         }
///
///         for __crepe_var in &__edge {
///             let x = __crepe_var.0;
///             let y = __crepe_var.1;
///             if let Some(__crepe_iter) = __tc_index_bf.get(&(y,)) {
///                 for __crepe_var in __crepe_iter {
///                     let z = __crepe_var.1;
///                     let __crepe_goal = Tc(x, z);
///                     if !__tc.contains(&__crepe_goal) {
///                         __tc_new.insert(__crepe_goal);
///                     }
///                 }
///             }
///         }
///
///         __tc_update = __tc_new;
///         __edge_update = __edge_new;
///         __crepe_first_iteration = false;
///     }
///
///     // Return value
///     (__tc,)
/// }
/// ```
/// Please note that this example uses naive evaluation for simplicity, but we
/// actually generate code for semi-naive evaluation.
fn make_run(context: &Context) -> proc_macro2::TokenStream {
    let mut indices: HashSet<Index> = HashSet::new();

    let main_loops = {
        let mut loop_wrappers = Vec::new();
        for stratum in context.strata.iter() {
            loop_wrappers.push(make_stratum(context, stratum, &mut indices));
        }
        loop_wrappers
            .iter()
            .zip(context.strata.iter())
            .map(|(f, stratum)| f(make_updates(context, stratum, &indices)))
            .collect::<proc_macro2::TokenStream>()
    };
    
    let main_loops_with_provenance = {
        let mut loop_wrappers = Vec::new();
        for stratum in context.strata.iter() {
            loop_wrappers.push(make_stratum_with_provenance(context, stratum, &mut indices.clone()));
        }
        loop_wrappers
            .iter()
            .zip(context.strata.iter())
            .map(|(f, stratum)| f(make_updates(context, stratum, &indices)))
            .collect::<proc_macro2::TokenStream>()
    };
    
    // Generate rule registrations
    let rule_registrations = context.rules.iter().enumerate().map(|(idx, rule)| {
        let goal_name = &rule.goal.relation;
        let rule_desc = format!("{} <- ...", goal_name);
        quote! {
            __crepe_provenance.register_rule(#idx, #rule_desc.to_string());
        }
    });
    
    // Generate per-rule provenance storage: just Vec<(usize, Vec<usize>)>
    let rule_storage_inits = context.rules.iter().enumerate().map(|(idx, _rule)| {
        let var_name = format_ident!("__crepe_rule_{}_provenance", idx);
        quote! {
            let mut #var_name: ::std::vec::Vec<(usize, ::std::vec::Vec<usize>)> = ::std::vec::Vec::new();
        }
    });
    
    // Collect per-rule storage into Provenance at the end
    let rule_storage_collections = context.rules.iter().enumerate().map(|(idx, _rule)| {
        let var_name = format_ident!("__crepe_rule_{}_provenance", idx);
        quote! {
            for (output_id, input_ids) in #var_name {
                __crepe_provenance.add_rule_application(#idx, output_id, input_ids);
            }
        }
    });

    let initialize = {
        let init_rels = context.all_relations().map(|rel| {
            let rel_ty = relation_type(rel, LifetimeUsage::Local);
            let lower = to_lowercase(&rel.name);
            let var = format_ident!("__{}", lower);
            let var_update = format_ident!("__{}_update", lower);

            quote! {
                let mut #var: ::std::collections::HashMap<#rel_ty, usize, CrepeHasher> =
                    ::std::collections::HashMap::default();
                let mut #var_update: ::std::collections::HashMap<#rel_ty, usize, CrepeHasher> =
                    ::std::collections::HashMap::default();
            }
        });
        
        // Global fact ID counter
        let init_id_counter = quote! {
            let mut __crepe_next_fact_id: usize = 0;
        };
        
        let init_indices = indices.iter().map(|index| {
            let rel = context
                .get_relation(&index.name.to_string())
                .expect("index relation should be found in context");
            let rel_ty = relation_type(rel, LifetimeUsage::Local);
            let index_name = index.to_ident();
            let key_type = index.key_type(context);

            quote! {
                let mut #index_name:
                    ::std::collections::HashMap<(#(#key_type,)*), ::std::vec::Vec<#rel_ty>, CrepeHasher> =
                    ::std::collections::HashMap::default();
            }
        });
        let load_inputs = context.rels_input.values().map(|rel| {
            let lower = to_lowercase(&rel.name);
            let var_update = format_ident!("__{}_update", lower);
            quote! {
                for fact in self.#lower {
                    #var_update.insert(fact, __crepe_next_fact_id);
                    __crepe_next_fact_id += 1;
                }
            }
        });
        
        quote! {
            #init_id_counter
            #(#init_rels)*
            #(#init_indices)*
            #(#load_inputs)*
        }
    };

    let output = {
        let output_fields = context.output_order.iter().map(|name| {
            let lower = to_lowercase(name);
            let var = format_ident!("__{}", lower);
            quote! {
                #var.into_keys().collect()
            }
        });
        quote! {
            (#(#output_fields,)*)
        }
    };
    
    let output_with_provenance = {
        let output_fields = context.output_order.iter().map(|name| {
            let lower = to_lowercase(name);
            let var = format_ident!("__{}", lower);
            quote! {
                #var.into_keys().collect()
            }
        });
        quote! {
            (#(#output_fields,)* __crepe_provenance)
        }
    };

    let output_ty_hasher = make_output_ty(context, quote! { CrepeHasher });
    let output_ty_default = make_output_ty(context, quote! {});
    let output_ty_provenance_hasher = make_output_ty_with_provenance(context, quote! { CrepeHasher });
    let output_ty_provenance_default = make_output_ty_with_provenance(context, quote! {});
    
    quote! {
        #[allow(clippy::collapsible_if)]
        fn run_with_hasher<CrepeHasher: ::std::hash::BuildHasher + ::core::default::Default>(
            self
        ) -> #output_ty_hasher {
            #initialize
            #main_loops
            #output
        }

        fn run(self) -> #output_ty_default {
            self.run_with_hasher::<::std::collections::hash_map::RandomState>()
        }
        
        #[allow(clippy::collapsible_if)]
        fn run_with_provenance_and_hasher<CrepeHasher: ::std::hash::BuildHasher + ::core::default::Default>(
            self
        ) -> #output_ty_provenance_hasher {
            let mut __crepe_provenance = Provenance::new();
            
            // Register all rule descriptions
            #(#rule_registrations)*
            
            // Initialize per-rule provenance storage
            #(#rule_storage_inits)*
            
            #initialize
            #main_loops_with_provenance
            
            // Collect provenance from per-rule storage
            #(#rule_storage_collections)*
            
            #output_with_provenance
        }
        
        fn run_with_provenance(self) -> #output_ty_provenance_default {
            self.run_with_provenance_and_hasher::<::std::collections::hash_map::RandomState>()
        }
    }
}

fn make_stratum(
    context: &Context,
    stratum: &[Ident],
    indices: &mut HashSet<Index>,
) -> Box<QuoteWrapper> {
    make_stratum_impl(context, stratum, indices, false)
}

fn make_stratum_with_provenance(
    context: &Context,
    stratum: &[Ident],
    indices: &mut HashSet<Index>,
) -> Box<QuoteWrapper> {
    make_stratum_impl(context, stratum, indices, true)
}

fn make_stratum_impl(
    context: &Context,
    stratum: &[Ident],
    indices: &mut HashSet<Index>,
    with_provenance: bool,
) -> Box<QuoteWrapper> {
    let stratum: HashSet<_> = stratum.iter().collect();
    let current_rels: Vec<_> = stratum
        .iter()
        .map(|name| {
            context
                .get_relation(&name.to_string())
                .expect("cannot find relation from stratum")
        })
        .collect();

    let empty_cond: proc_macro2::TokenStream = current_rels
        .iter()
        .map(|rel| {
            let lower = to_lowercase(&rel.name);
            let rel_update = format_ident!("__{}_update", lower);
            quote! {
                #rel_update.is_empty() &&
            }
        })
        .chain(std::iter::once(quote! {true}))
        .collect();

    let new_decls: proc_macro2::TokenStream = current_rels
        .iter()
        .map(|rel| {
            let rel_ty = relation_type(rel, LifetimeUsage::Local);
            let lower = to_lowercase(&rel.name);
            let rel_new = format_ident!("__{}_new", lower);
            quote! {
                let mut #rel_new: ::std::collections::HashMap<#rel_ty, usize, CrepeHasher> =
                    ::std::collections::HashMap::default();
            }
        })
        .collect();

    let rules: proc_macro2::TokenStream = context
        .rules
        .iter()
        .enumerate()
        .filter(|(_, rule)| stratum.contains(&rule.goal.relation))
        .map(|(rule_idx, rule)| {
            if with_provenance {
                make_rule_with_provenance(rule, rule_idx, &stratum, indices)
            } else {
                make_rule(rule, &stratum, indices)
            }
        })
        .collect();

    let set_update_to_new: proc_macro2::TokenStream = current_rels
        .iter()
        .map(|rel| {
            let lower = to_lowercase(&rel.name);
            let rel_update = format_ident!("__{}_update", lower);
            let rel_new = format_ident!("__{}_new", lower);
            quote! {
                #rel_update = #rel_new;
            }
        })
        .collect();

    // We can only compute the updates later, when all indices are known
    Box::new(move |updates| {
        quote! {
            let mut __crepe_first_iteration = true;
            while __crepe_first_iteration || !(#empty_cond) {
                #updates
                #new_decls
                #rules
                #set_update_to_new
                __crepe_first_iteration = false;
            }
        }
    })
}

fn make_updates(
    context: &Context,
    stratum: &[Ident],
    indices: &HashSet<Index>,
) -> proc_macro2::TokenStream {
    let rel_updates = stratum.iter().map(|name| {
        let lower = to_lowercase(name);
        let rel = format_ident!("__{}", lower);
        let rel_update = format_ident!("__{}_update", lower);
        quote! {
            #rel.extend(&#rel_update);
        }
    });
    let index_updates = indices.iter().filter_map(|index| {
        if !stratum.contains(&index.name) {
            return None;
        }

        let rel = context
            .get_relation(&index.name.to_string())
            .expect("index relation should be found in context");

        let rel_ty = relation_type(rel, LifetimeUsage::Local);
        let rel_update = format_ident!("__{}_update", to_lowercase(&rel.name));

        let index_name = index.to_ident();
        let index_name_update = format_ident!("{}_update", index_name);
        let key_type = index.key_type(context);
        let bound_pos = index.bound_pos();
        Some(quote! {
            let mut #index_name_update: ::std::collections::HashMap<
                (#(#key_type,)*),
                ::std::vec::Vec<#rel_ty>,
                CrepeHasher
            > = ::std::collections::HashMap::default();
            for __crepe_var in #rel_update.keys() {
                #index_name
                    .entry((#(__crepe_var.#bound_pos,)*))
                    .or_default()
                    .push(*__crepe_var);
                #index_name_update
                    .entry((#(__crepe_var.#bound_pos,)*))
                    .or_default()
                    .push(*__crepe_var);
            }
        })
    });
    rel_updates.chain(index_updates).collect()
}

fn make_rule(
    rule: &Rule,
    stratum: &HashSet<&Ident>,
    indices: &mut HashSet<Index>,
) -> proc_macro2::TokenStream {
    make_rule_impl(rule, 0, stratum, indices, false)
}

fn make_rule_with_provenance(
    rule: &Rule,
    rule_idx: usize,
    stratum: &HashSet<&Ident>,
    indices: &mut HashSet<Index>,
) -> proc_macro2::TokenStream {
    make_rule_impl(rule, rule_idx, stratum, indices, true)
}

fn make_rule_impl(
    rule: &Rule,
    rule_idx: usize,
    stratum: &HashSet<&Ident>,
    indices: &mut HashSet<Index>,
    with_provenance: bool,
) -> proc_macro2::TokenStream {
    let goal_relation = &rule.goal.relation;
    let goal_fields = &rule.goal.fields;
    let name = format_ident!("__{}", to_lowercase(goal_relation));
    let name_new = format_ident!("__{}_new", to_lowercase(goal_relation));
    
    let goal = if with_provenance {
        let rule_storage = format_ident!("__crepe_rule_{}_provenance", rule_idx);
        quote! {
            let __crepe_goal = #goal_relation(#goal_fields);
            if !#name.contains_key(&__crepe_goal) {
                let __crepe_output_id = __crepe_next_fact_id;
                __crepe_next_fact_id += 1;
                #name_new.insert(__crepe_goal, __crepe_output_id);
                
                // Store the derivation: (output_id, vec_of_input_ids)
                #rule_storage.push((__crepe_output_id, __crepe_input_facts.clone()));
            }
        }
    } else {
        quote! {
            let __crepe_goal = #goal_relation(#goal_fields);
            if !#name.contains_key(&__crepe_goal) {
                #name_new.insert(__crepe_goal, 0);  // ID doesn't matter without provenance
            }
        }
    };
    
    let fact_positions: Vec<_> = rule
        .clauses
        .iter()
        .enumerate()
        .filter_map(|(i, clause)| match clause {
            Clause::Fact(fact) => {
                if stratum.contains(&fact.relation) {
                    Some(i)
                } else {
                    None
                }
            }
            _ => None,
        })
        .collect();
    if fact_positions.is_empty() {
        // Will not change, so we only need to evaluate it once
        let mut datalog_vars: HashSet<String> = HashSet::new();
        #[allow(clippy::needless_collect)]
        let fragments: Vec<_> = rule
            .clauses
            .iter()
            .cloned()
            .enumerate()
            .map(|(i, clause)| {
                make_clause(clause, false, &mut datalog_vars, indices, with_provenance, i == 0)
            })
            .collect();
        
        let eval_loop = fragments.into_iter().rev().fold(goal, |x, f| f(x));
        
        if with_provenance {
            quote! {
                if __crepe_first_iteration {
                    let mut __crepe_input_facts: ::std::vec::Vec<usize> = ::std::vec::Vec::new();
                    #eval_loop
                }
            }
        } else {
            quote! {
                if __crepe_first_iteration {
                    #eval_loop
                }
            }
        }
    } else {
        // Rule has one or more facts, so we use semi-naive evaluation
        let mut variants = Vec::new();
        for update_position in fact_positions {
            let mut datalog_vars: HashSet<String> = HashSet::new();
            #[allow(clippy::needless_collect)]
            let fragments: Vec<_> = rule
                .clauses
                .iter()
                .cloned()
                .enumerate()
                .map(|(i, clause)| {
                    make_clause(clause, update_position == i, &mut datalog_vars, indices, with_provenance, i == 0)
                })
                .collect();
            
            let eval_loop = fragments.into_iter().rev().fold(goal.clone(), |x, f| f(x));
            
            if with_provenance {
                variants.push(quote! {
                    let mut __crepe_input_facts: ::std::vec::Vec<usize> = ::std::vec::Vec::new();
                    #eval_loop
                });
            } else {
                variants.push(eval_loop);
            }
        }
        variants.into_iter().collect()
    }
}

fn make_clause(
    clause: Clause,
    only_update: bool,
    datalog_vars: &mut HashSet<String>,
    indices: &mut HashSet<Index>,
    with_provenance: bool,
    is_first_clause: bool,
) -> Box<QuoteWrapper> {
    match clause {
        Clause::Fact(fact) => {
            let name = &fact.relation;
            if fact.negate.is_some() {
                // Special case: stratified negation, needs to be handled separately
                assert!(!only_update);
                let to_mode = |f: &FactField| match f {
                    FactField::Ignored(_) => IndexMode::Free,
                    FactField::Ref(_, ident) => {
                        abort!(ident, "Unable to bind values in negated clause")
                    }
                    FactField::Expr(_) => IndexMode::Bound,
                };
                let index = Index {
                    name: name.clone(),
                    mode: fact.fields.iter().map(to_mode).collect(),
                };
                let index_name = index.to_ident();
                indices.insert(index);
                let bound_fields: Vec<_> = fact
                    .fields
                    .iter()
                    .filter(|t| matches!(t, FactField::Expr(_)))
                    .cloned()
                    .collect();
                return Box::new(move |body| {
                    quote_spanned! {fact.relation.span()=>
                        if !#index_name.contains_key(&(#(#bound_fields,)*)) {
                            #body
                        }
                    }
                });
            }
            let mut setters = Vec::new();
            let mut index_mode = Vec::new();
            for (i, field) in fact.fields.iter().enumerate() {
                let idx = syn::Index::from(i);
                match field {
                    FactField::Ignored(_) => index_mode.push(IndexMode::Free),
                    FactField::Ref(_, ident) => {
                        index_mode.push(IndexMode::Free);
                        datalog_vars.insert(ident.to_string());
                        setters.push(quote! {
                            let #ident = &__crepe_var.#idx;
                        });
                    }
                    FactField::Expr(expr) => {
                        if let Some(var) = is_datalog_var(expr) {
                            let var_name = var.to_string();
                            if datalog_vars.contains(&var_name) {
                                index_mode.push(IndexMode::Bound);
                            } else {
                                index_mode.push(IndexMode::Free);
                                datalog_vars.insert(var_name);
                                setters.push(quote! {
                                    let #field = __crepe_var.#idx;
                                });
                            }
                        } else {
                            index_mode.push(IndexMode::Bound);
                        }
                    }
                }
            }
            let setters: proc_macro2::TokenStream = setters.into_iter().collect();
            
            let provenance_record = if with_provenance {
                let lower = to_lowercase(name);
                let rel_var = if only_update {
                    format_ident!("__{}_update", lower)
                } else {
                    format_ident!("__{}", lower)
                };
                quote! {
                    if let Some(&fact_id) = #rel_var.get(__crepe_var) {
                        __crepe_input_facts.push(fact_id);
                    }
                }
            } else {
                quote! {}
            };
            
            let clear_inputs = if with_provenance && is_first_clause {
                quote! { __crepe_input_facts.clear(); }
            } else {
                quote! {}
            };

            if !index_mode.contains(&IndexMode::Bound) {
                let mut rel = format_ident!("__{}", &to_lowercase(name));
                if only_update {
                    rel = format_ident!("{}_update", rel);
                }
                // If no fields are bound, we don't need an index
                Box::new(move |body| {
                    quote_spanned! {fact.relation.span()=>
                        for __crepe_var in #rel.keys() {
                            #clear_inputs
                            #setters
                            #provenance_record
                            #body
                        }
                    }
                })
            } else {
                // Otherwise, we're going to need an index!
                let bound_fields: Vec<_> = index_mode
                    .iter()
                    .zip(fact.fields.iter())
                    .filter_map(|(mode, field)| match mode {
                        IndexMode::Bound => Some(field.clone()),
                        IndexMode::Free => None,
                    })
                    .collect();
                let index = Index {
                    name: name.clone(),
                    mode: index_mode,
                };
                let mut index_name = Ident::new(&index.to_string(), name.span());
                if only_update {
                    index_name = format_ident!("{}_update", index_name);
                }
                indices.insert(index);
                Box::new(move |body| {
                    quote_spanned! {fact.relation.span()=>
                        if let Some(__crepe_iter) = #index_name.get(&(#(#bound_fields,)*)) {
                            for __crepe_var in __crepe_iter {
                                #clear_inputs
                                #setters
                                #provenance_record
                                #body
                            }
                        }
                    }
                })
            }
        }
        Clause::Expr(expr) => {
            assert!(!only_update);
            Box::new(move |body| {
                quote! {
                    #[allow(unused_parens)]
                    if #expr { #body }
                }
            })
        }
        Clause::Let(guard) => {
            assert!(!only_update);
            pat_datalog_vars(&guard.pat, datalog_vars);
            Box::new(move |body| {
                quote! {
                    #[allow(irrefutable_let_patterns)]
                    if #guard { #body }
                }
            })
        }
        Clause::For(For { pat, expr, .. }) => {
            assert!(!only_update);
            Box::new(move |body| {
                quote! {
                    for #pat in #expr { #body }
                }
            })
        }
    }
}

fn make_output_ty(context: &Context, hasher: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    let fields = context.output_order.iter().map(|name| {
        let rel = context.rels_output.get(&name.to_string()).unwrap();
        relation_type(rel, LifetimeUsage::Item)
    });

    quote! {
        (#(::std::collections::HashSet<#fields, #hasher>,)*)
    }
}

fn make_output_ty_with_provenance(context: &Context, hasher: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    let fields = context.output_order.iter().map(|name| {
        let rel = context.rels_output.get(&name.to_string()).unwrap();
        relation_type(rel, LifetimeUsage::Item)
    });

    quote! {
        (#(::std::collections::HashSet<#fields, #hasher>,)* Provenance)
    }
}

/// Returns whether an expression in a relation is a Datalog variable.
///
/// - `is_datalog_var(x) => Some(Ident("x"))`
/// - `is_datalog_var(_helloWorld) => Some(Ident("_helloWorld"))`
/// - `is_datalog_var(x + y) => None`
/// - `is_datalog_var(StartsWithCapitalLetter) => None`
/// - `is_datalog_var(true) => None`
fn is_datalog_var(expr: &Expr) -> Option<Ident> {
    use syn::{ExprPath, Path, PathArguments};
    match expr {
        Expr::Path(ExprPath {
            attrs,
            qself: None,
            path:
                Path {
                    leading_colon: None,
                    segments,
                },
        }) => {
            if attrs.is_empty() && segments.len() == 1 {
                let segment = segments.iter().next()?;
                if let PathArguments::None = segment.arguments {
                    let ident = segment.ident.clone();
                    match ident.to_string().chars().next() {
                        Some('a'..='z') | Some('_') => return Some(ident),
                        _ => (),
                    }
                }
            }
            None
        }
        _ => None,
    }
}

/// Visits a pattern in `ExprLet` position, returning all Datalog variables that
/// are bound by that pattern.
fn pat_datalog_vars(pat: &Pat, datalog_vars: &mut HashSet<String>) {
    match pat {
        Pat::Const(_) => (),
        Pat::Ident(pi) => {
            datalog_vars.insert(pi.ident.to_string());
            if let Some((_, ref p)) = pi.subpat {
                pat_datalog_vars(p, datalog_vars);
            }
        }
        Pat::Lit(_) => (),
        Pat::Macro(pm) => abort!(pm.span(), "Macros not allowed in let bindings."),
        Pat::Or(_) => (),
        Pat::Paren(pp) => pat_datalog_vars(&pp.pat, datalog_vars),
        Pat::Path(_) => (),
        Pat::Range(_) => (),
        Pat::Reference(pr) => pat_datalog_vars(&pr.pat, datalog_vars),
        Pat::Rest(_) => (),
        Pat::Slice(ps) => {
            for e in &ps.elems {
                pat_datalog_vars(e, datalog_vars);
            }
        }
        Pat::Struct(ps) => {
            for field_pat in &ps.fields {
                pat_datalog_vars(&field_pat.pat, datalog_vars);
            }
        }
        Pat::Tuple(pt) => {
            for e in &pt.elems {
                pat_datalog_vars(e, datalog_vars);
            }
        }
        Pat::TupleStruct(pts) => {
            for e in &pts.elems {
                pat_datalog_vars(e, datalog_vars);
            }
        }
        Pat::Type(pt) => pat_datalog_vars(&pt.pat, datalog_vars),
        Pat::Verbatim(pv) => abort!(pv.span(), "Cannot parse verbatim pattern."),
        Pat::Wild(_) => (),
        _ => abort!(pat.span(), "Unsupported pattern type."),
    }
}

/// Converts an `Ident` to lowercase, with the same `Span`
fn to_lowercase(name: &Ident) -> Ident {
    let s = name.to_string().to_lowercase();
    Ident::new(&s, name.span())
}

/// Validate generic parameters on a relation
/// Checks for unsupported features and provides helpful error messages
fn validate_generic_params(relation: &Relation) {
    // Type parameters are now supported!
    // Const parameters are not yet supported
    if let Some(c) = relation.generics.const_params().next() {
        abort!(c.span(), "Const parameters are not yet supported in relations");
    }
    
    // Where clauses are not yet supported
    if let Some(where_clause) = &relation.generics.where_clause {
        abort!(
            where_clause.where_token.span(), 
            "Where clauses are not yet supported in relations. \
             Please specify trait bounds directly on the type parameter instead, e.g., `T: Trait`"
        );
    }
    
    // Check for default type parameters (not supported)
    for type_param in relation.generics.type_params() {
        if type_param.default.is_some() {
            abort!(
                type_param.ident.span(),
                "Default type parameters are not supported in relations. \
                 Please remove the default value from type parameter `{}`",
                type_param.ident
            );
        }
    }
    
    // Check for lifetime bounds (not supported)
    for lifetime_param in relation.generics.lifetimes() {
        if !lifetime_param.bounds.is_empty() {
            abort!(
                lifetime_param.lifetime.span(),
                "Lifetime bounds are not supported in relations. \
                 Please remove bounds from lifetime parameter `{}`",
                lifetime_param.lifetime
            );
        }
    }
}

/// Collect all unique type parameters from input relations
fn collect_generic_params(context: &Context) -> Vec<&syn::TypeParam> {
    let mut seen = HashSet::new();
    let mut params = Vec::new();
    
    for relation in context.rels_input.values() {
        for param in relation.generics.type_params() {
            if seen.insert(param.ident.to_string()) {
                params.push(param);
            }
        }
    }
    
    params
}

/// Check if a type parameter has a specific trait bound
fn has_bound(tp: &syn::TypeParam, bound_name: &str) -> bool {
    tp.bounds.iter().any(|b| match b {
        syn::TypeParamBound::Trait(trait_bound) => {
            trait_bound.path.segments.last()
                .map_or(false, |seg| seg.ident == bound_name)
        }
        _ => false,
    })
}

/// Required trait bounds for all generic types in Datalog relations
const REQUIRED_BOUNDS: &[&str] = &["Hash", "Eq", "Clone", "Copy", "Default"];

/// Get the TokenStream for a required bound
fn required_bound_token(name: &str) -> proc_macro2::TokenStream {
    match name {
        "Hash" => quote! { ::std::hash::Hash },
        "Eq" => quote! { ::std::cmp::Eq },
        "Clone" => quote! { ::std::clone::Clone },
        "Copy" => quote! { ::std::marker::Copy },
        "Default" => quote! { ::std::default::Default },
        _ => panic!("Unknown required bound: {}", name),
    }
}

/// Merge user bounds with required bounds, avoiding duplicates
fn merge_bounds_with_required(tp: &syn::TypeParam) -> proc_macro2::TokenStream {
    let ident = &tp.ident;
    let user_bounds = &tp.bounds;
    
    // Collect missing required bounds
    let missing_bounds: Vec<_> = REQUIRED_BOUNDS.iter()
        .filter(|&req| !has_bound(tp, req))
        .map(|req| required_bound_token(req))
        .collect();
    
    // Combine user bounds + missing required bounds
    match (user_bounds.is_empty(), missing_bounds.is_empty()) {
        (true, true) => quote! { #ident },  // No bounds at all (shouldn't happen)
        (true, false) => quote! { #ident: #(#missing_bounds)+* },
        (false, true) => quote! { #ident: #user_bounds },
        (false, false) => quote! { #ident: #user_bounds + #(#missing_bounds)+* },
    }
}

/// Helper to format generic parameters with angle brackets
/// Returns `<item1, item2, ...>` or empty if the list is empty
fn format_generics(items: Vec<proc_macro2::TokenStream>) -> proc_macro2::TokenStream {
    if items.is_empty() { quote! {} } else { quote! { <#(#items),*> } }
}

/// Create a tokenstream for generic parameters (lifetimes + type params)
fn generic_params_decl(context: &Context) -> proc_macro2::TokenStream {
    let mut items = Vec::new();
    if context.has_input_lifetime {
        items.push(quote! { 'a });
    }
    items.extend(collect_generic_params(context).into_iter().map(merge_bounds_with_required));
    format_generics(items)
}

/// Create a tokenstream for generic arguments (just the names, no bounds)
fn generic_params_args(context: &Context) -> proc_macro2::TokenStream {
    let mut items = Vec::new();
    if context.has_input_lifetime {
        items.push(quote! { 'a });
    }
    items.extend(collect_generic_params(context).into_iter().map(|tp| {
        let ident = &tp.ident;
        quote! { #ident }
    }));
    format_generics(items)
}

enum LifetimeUsage {
    Item,
    Local,
}

/// Returns the type of a relation, with appropriate lifetimes and type parameters
fn relation_type(rel: &Relation, usage: LifetimeUsage) -> proc_macro2::TokenStream {
    let symbol = match rel.relation_type().unwrap() {
        RelationType::Input | RelationType::Output => "'a",
        RelationType::Intermediate => match usage {
            LifetimeUsage::Item => "'a",
            LifetimeUsage::Local => "'_",
        },
    };

    let name = &rel.name;
    
    // Build list of generic arguments
    let mut items = Vec::new();
    items.extend(rel.generics.lifetimes().map(|l| {
        let lifetime = Lifetime::new(symbol, l.span());
        quote! { #lifetime }
    }));
    items.extend(rel.generics.type_params().map(|tp| {
        let ident = &tp.ident;
        quote! { #ident }
    }));
    
    // Format with angle brackets if there are any generics
    if items.is_empty() {
        quote! { #name }
    } else {
        quote! { #name<#(#items),*> }
    }
}
