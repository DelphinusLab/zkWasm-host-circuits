use std::ops::BitXor;

/* define atomic functions
 * fn  f(x, y, z)        ((x) ^ (y) ^ (z))
 * fn  g(x, y, z)        (((x) & (y)) | (~(x) & (z)))
 * fn  g(x, y, z)        (((x) | ~(y)) ^ (z))
 * fn  i(x, y, z)        (((x) & (z)) | ((y) & ~(z)))
 * fn  j(x, y, z)        ((x) ^ ((y) | ~(z)))
 */
pub trait RMD160Atomic{
    fn f(x: Self, y: Self, z: Self) -> Self;
    fn g(x: Self, y: Self, z: Self) -> Self;
    fn h(x: Self, y: Self, z: Self) -> Self;
    fn i(x: Self, y: Self, z: Self) -> Self;
    fn j(x: Self, y: Self, z: Self) -> Self;
}

impl RMD160Atomic for u32 {
    fn f(x: u32, y: u32, z: u32) -> u32 {
        x ^ y ^ z
    }
    fn g(x: u32, y: u32, z: u32) -> u32 {
        (x & y) | ((!x) & z)
    }
    fn h(x: u32, y: u32, z: u32) -> u32 {
        (x | (!y)) ^ z
    }
    fn i(x: u32, y: u32, z: u32) -> u32 {
        (x & z) | (y & (!z))
    }

    fn j(x: u32, y: u32, z: u32) -> u32 {
        x ^ (y | (!z))
    }
}

fn rol_modifier(round: usize, rol: &mut Vec<u32>, x: u32, offset: u32, shift: u32) {
    println!("length of rol {:?}", rol);
    rol[0] = match round {
        0 => u32::f(rol[1], rol[2], rol[3]),
        1 => u32::g(rol[1], rol[2], rol[3]),
        2 => u32::h(rol[1], rol[2], rol[3]),
        3 => u32::i(rol[1], rol[2], rol[3]),
        4 => u32::j(rol[1], rol[2], rol[3]),
        _ => unreachable!(),
    };
    rol[0] = rol[0].overflowing_add(x).0.overflowing_add(offset).0;
    rol[0] = rol[0].rotate_left(shift).overflowing_add(rol[4]).0;
    rol[2] = rol[2].rotate_left(10);
    rol.rotate_right(1);
}

pub(crate) const INITBUF: [u32; 5] = [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0];

pub(crate) const ROUNDS_OFFSET: [u32; 5] = [
    0x0, 0x5a827999, 0x6ed9eba1, 0x8f1bbcdc, 0xa953fd4e,
];

pub(crate) const PROUNDS_OFFSET: [u32; 5] = [
    0, 0x7a6d76e9, 0x6d703ef3, 0x5c4dd124, 0x50a28be6,
];

/*round1*/
pub(crate) const R: [[u32; 16]; 5] = [
    [11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8],
    [7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12],
    [11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5],
    [11, 12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12],
    [9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6],
];

pub(crate) const O: [[usize; 16]; 5] = [
    [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],
    [7,4,13,1,10,6,15,3,12,0,9,5,2,14,11,8],
    [3,10,14,4,9,15,8,1,2,7,0,6,13,11,5,12],
    [1,9,11,10,0,8,12,4,13,3,7,15,14,5,6,2],
    [4,0,5,9,7,12,2,10,14,1,3,8,11,6,15,13],
];

/*parallelround1*/
pub(crate) const PR: [[u32; 16]; 5] = [
    [8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6],
    [9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7, 6, 15, 13, 11],
    [9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5],
    [15, 5, 8, 11, 14, 14, 6, 14, 6, 9, 12, 9, 12, 5, 15, 8],
    [8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11],
];

pub(crate) const PO: [[usize; 16]; 5] = [
    [5,14,7,0,9,2,11,4,13,6,15,8,1,10,3,12],
    [6,11,3,7,0,13,5,10,14,15,8,12,4,9,1,2],
    [15,5,1,3,7,14,6,9,11,8,12,2,10,0,4,13],
    [8,6,4,1,3,11,15,0,5,12,2,13,9,7,10,14],
    [12,15,10,4,1,5,8,7,6,2,13,14,0,3,9,11],
];

pub fn gen_modifier_witness(rol: &[u32; 5], x: u32, shift:u32, offset:u32) -> [u32; 4] {
    let w0 = u32::f(rol[1], rol[2], rol[3]);
    let w1 = w0 + x + offset;
    let w2 = w1.rotate_left(shift) + rol[4];
    let w3 = rol[2].rotate_left(10);
    [w0,w1,w2,w3]
}

fn compress(w: &Vec<u32>, values: Vec<u32>) -> Vec<u32> {
    let mut rol1 = w.clone();
    let mut rol2 = w.clone();
    let mut round = 0;
    for ((idxs,shift), offset) in O.zip(R).zip(ROUNDS_OFFSET) {
        for limb_index in 0..16 {
            let idx = idxs[limb_index];
            rol_modifier(round, &mut rol1, values[idx], offset, shift[idx]);
        }
        round += 1;
    }
    round = 0;
    for ((idxs,shift), offset) in PO.zip(PR).zip(PROUNDS_OFFSET) {
        for limb_index in 0..16 {
            let idx = idxs[limb_index];
            rol_modifier(round, &mut rol2, values[idx], offset, shift[idx]);
        }
        round += 1;
    }
    let mut r = vec![];
    for i in 0..w.len() {
        r.push(w[i].overflowing_add(rol1[i]).0.overflowing_add(rol2[(i+1)%w.len()]).0);
    }
    r.rotate_left(1);
    r
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_rmd160_compress() {
        let w = super::INITBUF.to_vec().clone();
        let r = super::compress(&w, [0u32; 16].to_vec());
        println!("{:?}", r);
    }
}
