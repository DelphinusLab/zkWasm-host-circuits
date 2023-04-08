use lazy_static::lazy_static;
use rand::rngs::OsRng;

const TREE_LAYERS: usize = PATH_LEN + 1;

// The number of rows used in the constraint system matrix (two rows per path element).
const N_ROWS_USED: usize = 2 * PATH_LEN;
const LAST_ROW: usize = N_ROWS_USED - 1;



struct Tree(Vec<Vec<Fp>>);

impl Tree {
    fn rand() -> Self {
        let mut rng = thread_rng();
        let leafs: Vec<Fp> = (0..N_LEAFS).map(|_| Fp::random(&mut rng)).collect();
        let mut layers = vec![leafs];
        for l in 1..TREE_LAYERS {
            let layer: Vec<Fp> = layers[l - 1]
                .chunks(2)
                .map(|pair| mock_hash(pair[0], pair[1]))
                .collect();
            layers.push(layer)
        }
        assert_eq!(layers.last().unwrap().len(), 1);
        Tree(layers)
    }

    fn root(&self) -> Fp {
        self.0.last().unwrap()[0]
    }

    fn leafs(&self) -> &[Fp] {
        self.0.first().unwrap()
    }

    fn gen_path(&self, c: usize) -> Vec<Fp> {
        let mut path = vec![];
        let mut node_index = c;
        for layer in 0..PATH_LEN {
            let sib = if node_index & 1 == 0 {
                self.0[layer][node_index + 1].clone()
            } else {
                self.0[layer][node_index - 1].clone()
            };
            path.push(sib);
            node_index /= 2;
        }
        path
    }
}

fn test() {
    assert!(N_LEAFS.is_power_of_two());

    // Generate a Merkle tree from random data.
    let tree = Tree::rand();

    // Generate a random challenge, i.e. a leaf index in `[0, N_LEAFS)`.
    let c: usize = thread_rng().gen_range(0..N_LEAFS);
    let c_bits: Vec<Fp> = (0..PATH_LEN)
        .map(|i| {
            if (c >> i) & 1 == 0 {
                Fp::zero()
            } else {
                Fp::one()
            }
        })
        .collect();

    // Create the public inputs. Every other row in the constraint system has a public input for a
    // challenge bit, additionally the last row has a public input for the root.
    let k = (N_ROWS_USED as f32).log2().ceil() as u32;
    let mut pub_inputs = vec![Fp::zero(); 1 << k];
    for i in 0..PATH_LEN {
        pub_inputs[2 * i] = c_bits[i].clone();
    }
    pub_inputs[LAST_ROW] = tree.root();

    // Assert that the constraint system is satisfied for a witness corresponding to `pub_inputs`.
    let circuit = MerkleCircuit {
        leaf: Some(tree.leafs()[c].clone()),
        path: Some(tree.gen_path(c)),
        c_bits: Some(c_bits),
    };
    let prover = MockProver::run(k, &circuit, vec![pub_inputs.clone()]).unwrap();
    assert!(prover.verify().is_ok());

    // Assert that changing the public challenge causes the constraint system to become unsatisfied.
    let mut bad_pub_inputs = pub_inputs.clone();
    bad_pub_inputs[0] = if pub_inputs[0] == Fp::zero() {
        Fp::one()
    } else {
        Fp::zero()
    };
    let prover = MockProver::run(k, &circuit, vec![bad_pub_inputs]).unwrap();
    let res = prover.verify();
    assert!(res.is_err());
    if let Err(errors) = res {
        assert_eq!(errors.len(), 1);
        if let VerifyFailure::Gate { gate_name, row, .. } = errors[0] {
            assert_eq!(gate_name, "public input");
            assert_eq!(row, 0);
        } else {
            panic!("expected public input gate failure");
        }
    }

    // Assert that changing the public root causes the constraint system to become unsatisfied.
    let mut bad_pub_inputs = pub_inputs.clone();
    bad_pub_inputs[LAST_ROW] += Fp::one();
    let prover = MockProver::run(k, &circuit, vec![bad_pub_inputs]).unwrap();
    let res = prover.verify();
    assert!(res.is_err());
    if let Err(errors) = res {
        assert_eq!(errors.len(), 1);
        if let VerifyFailure::Gate { gate_name, row, .. } = errors[0] {
            assert_eq!(gate_name, "public input");
            assert_eq!(row, LAST_ROW);
        } else {
            panic!("expected public input gate failure");
        }
    }

    // Assert that a non-boolean challenge bit causes the boolean constrain and swap gates to fail.
    let mut bad_pub_inputs = pub_inputs.clone();
    bad_pub_inputs[0] = Fp::from(2);
    let mut bad_circuit = circuit.clone();
    bad_circuit.c_bits.as_mut().unwrap()[0] = Fp::from(2);
    let prover = MockProver::run(k, &bad_circuit, vec![bad_pub_inputs]).unwrap();
    let res = prover.verify();
    assert!(res.is_err());
    if let Err(errors) = res {
        assert_eq!(errors.len(), 2);
        if let VerifyFailure::Gate { gate_name, row, .. } = errors[0] {
            assert_eq!(gate_name, "boolean constrain");
            assert_eq!(row, 0);
        } else {
            panic!("expected boolean constrain gate failure");
        }
        if let VerifyFailure::Gate { gate_name, row, .. } = errors[1] {
            assert_eq!(gate_name, "swap");
            assert_eq!(row, 0);
        } else {
            panic!("expected swap gate failure");
        }
    }

    // Assert that changing the witnessed path causes the constraint system to become unsatisfied
    // when checking that the calculated root is equal to the public input root.
    let mut bad_circuit = circuit.clone();
    bad_circuit.path.as_mut().unwrap()[0] += Fp::one();
    let prover = MockProver::run(k, &bad_circuit, vec![pub_inputs.clone()]).unwrap();
    let res = prover.verify();
    assert!(res.is_err());
    if let Err(errors) = res {
        assert_eq!(errors.len(), 1);
        if let VerifyFailure::Gate { gate_name, row, .. } = errors[0] {
            assert_eq!(gate_name, "public input");
            assert_eq!(row, LAST_ROW);
        } else {
            panic!("expected public input gate failure");
        }
    }
}
