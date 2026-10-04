use cordis_kernel::progress::{support, DagError};

#[test]
fn all_small_dags_match_the_unique_support_fixed_point() {
    for n in 0..=4 {
        let possible: Vec<_> = (0..n).flat_map(|i| (0..i).map(move |p| (i, p))).collect();
        for mask in 0..(1usize << possible.len()) {
            let mut edges = vec![Vec::new(); n];
            for (bit, &(i, p)) in possible.iter().enumerate() {
                if mask & (1 << bit) != 0 {
                    edges[i].push(p);
                }
            }
            for enabled_mask in 0..(1usize << n) {
                let enabled: Vec<_> = (0..n).map(|i| enabled_mask & (1 << i) != 0).collect();
                let actual = support(enabled.clone(), edges.clone()).unwrap();
                let candidates: Vec<Vec<bool>> = (0..(1usize << n))
                    .map(|m| (0..n).map(|i| m & (1 << i) != 0).collect::<Vec<_>>())
                    .filter(|s| {
                        (0..n).all(|i| s[i] == (enabled[i] && edges[i].iter().all(|&p| s[p])))
                    })
                    .collect();
                assert_eq!(candidates, vec![actual]);
            }
        }
    }
}

#[test]
fn rejects_unranked_input_even_when_disabled() {
    assert_eq!(support(vec![true], vec![]), Err(DagError::Shape));
    assert_eq!(
        support(vec![false], vec![vec![0]]),
        Err(DagError::NotTopological)
    );
    assert_eq!(
        support(vec![true, true], vec![vec![1], vec![0]]),
        Err(DagError::NotTopological)
    );
    assert_eq!(
        support(vec![true], vec![vec![usize::MAX]]),
        Err(DagError::NotTopological)
    );
}

#[test]
fn retirement_and_missing_provider_remove_transitive_support() {
    let edges = vec![vec![], vec![0], vec![0], vec![1, 2], vec![]];
    assert_eq!(
        support(vec![true, false, true, true, true], edges).unwrap(),
        vec![true, false, true, false, true]
    );
}
