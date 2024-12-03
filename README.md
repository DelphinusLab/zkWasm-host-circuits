# zkWasm-host-circuits

The host circuits contain two components. The operands selection circuit which selects the target opcodes and the host function constraint circuit which enforces the semantics of a specific host function.

## Operands selection circuit.
Suppose we have a host calling trace that calls two functions
```
a(x,y) = x + y + 1
b(x,y,z) = x * y * z
```

It follows that the shared host op table will look like the following:

| op_code | arg | idx |
| --------|-----|-----|
| 0       |   0 |  0  |
| op_a    | a_0 |  1  |
| op_a    | a_1 |  2  |
| op_a    | a_r |  3  |
| op_b    | b_0 |  4  |
| op_b    | b_1 |  5  |
| op_b    | b_2 |  6  |
| op_b    | b_r |  7  |

Thus, to implement the selection circuit for function ``b`` then the following should be the filtered result 

| op_code | arg_sel | idx_sel | 
| --------|-------- | --------|
| op_b    | $b_0$   |  4      |
| op_b    | $b_1$   |  5      |
| op_b    | $b_2$   |  6      |
| op_b    | $b_r$   |  7      |

# Appendix:
## configuring async backend
There are two async backend for mongodb: `mongo-std-sync` and `mongo-tokio-sync`(default). Note that when using the non-default backend`mongo-std-sync`, you must also using `default-features = false`.
