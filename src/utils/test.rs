use crate::customized_curcuits;
use crate::table_item;
use crate::item_count;

customized_curcuits!(RMD160Config, 5, 10, 7, 1, 2,
    | h_sel |  r_sel | a   | b     | c    |  d   | x    | e     | c_next |  offset
    | nil   |  nil   | w0  | b0    | c0   |  d0  | r0   | w1_h  | w4_h   |  w1_r
    | nil   |  nil   | wb  | b1    | c1   |  d1  | r1   | w1_l  | w4_l   |  w4_r
    | nil   |  nil   | wc  | b2    | c2   |  d2  | r2   | a_next| w2b    |   nil
    | nil   |  nil   | w1  | b3    | c3   |  d3  | r3   |  nil  | w2c    |   nil
);