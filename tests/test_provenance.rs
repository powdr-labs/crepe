// Test provenance tracking functionality

mod datalog {
    use crepe::crepe;

    crepe! {
        @input
        struct Edge(i32, i32);

        @output
        struct Reachable(i32, i32);

        Reachable(x, y) <- Edge(x, y);
        Reachable(x, z) <- Edge(x, y), Reachable(y, z);
    }

    pub fn run_with_provenance(edges: &[(i32, i32)]) -> (Vec<(i32, i32)>, Provenance) {
        let mut runtime = Crepe::new();
        runtime.extend(edges.iter().map(|&(a, b)| Edge(a, b)));
        let (reachable, provenance) = runtime.run_with_provenance();
        (
            reachable.into_iter().map(|Reachable(a, b)| (a, b)).collect(),
            provenance,
        )
    }
}

#[test]
fn test_provenance_tracking() {
    let edges = vec![(1, 2), (2, 3), (3, 4)];
    let (reachable, provenance) = datalog::run_with_provenance(&edges);
    
    // Check that we got the expected results
    let mut sorted_reachable = reachable.clone();
    sorted_reachable.sort_unstable();
    assert_eq!(
        sorted_reachable,
        vec![(1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]
    );
    
    // Check that provenance was recorded
    assert!(provenance.derivation_count() > 0, "Provenance should track derivations");
    
    println!("\n{}", provenance.display());
}

#[test]
fn test_provenance_rules() {
    let edges = vec![(1, 2), (2, 3)];
    let (_reachable, provenance) = datalog::run_with_provenance(&edges);
    
    // Check that rules were registered
    let rules = provenance.all_rule_descriptions();
    assert_eq!(rules.len(), 2, "Should have 2 rules");
    
    // Check rule descriptions
    for (id, desc) in rules {
        println!("Rule {}: {}", id, desc);
        assert!(desc.contains("Reachable"));
    }
}

#[test]
fn test_provenance_stats() {
    let edges = vec![(1, 2), (2, 3), (3, 4)];
    let (_reachable, provenance) = datalog::run_with_provenance(&edges);
    
    let deriv_count = provenance.derivation_count();
    
    println!("Derivations: {}", deriv_count);
    
    assert!(deriv_count > 0);
}
