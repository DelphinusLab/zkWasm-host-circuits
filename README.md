# zkWasm-host-circuits
## shared_op_table
a_0(x,y) = x + y + 1
| op_code | arg | is_ret | idx |
| --------|-----|--------| ----|
| 0       |   0 |  0     | 0   |
| op_a    | a_0 |  0     | 1   |
| op_a    | a_1 |  0     | 2   |
| op_a    | a_r |  1     | 3   |
| op_b    | b_0 |  0     | 4   |
| op_b    | b_1 |  1     | 5   |
| op_b    | b_0'|  0     | 6   |
| op_b    | b_1 |  1     | 7   |

## selected_op_table

| op_code | arg     | is_ret | idx_sel | 
| --------|-------- | -------| --------|
| op_b    | $b_0$   | 0      |  4      |
| op_b    | $b_1$   | 1      |  5      |
| op_b    | $b_0'$  | 0      |  6      |
| op_b    | $b_1'$  | 1      |  7      |

## configuring async backend
There are two async backend for mongodb: `mongo-std-sync` and `mongo-tokio-sync`(default). Note that when using the non-default backend`mongo-std-sync`, you must also using `default-features = false`.

## Server and Prover
Using the scripts `run.sh` and `runserver.sh` will start 2 applications in normal mode and REST server mode respectively. Please supply arguments in the scripts before running them.
