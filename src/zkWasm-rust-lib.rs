pub struct KeccakHasher (u64);

impl KeccakHasher {
    pub fn new() -> Self {
        unsafe {
            keccak_new(1u64);
        }
        KeccakHasher(0u64)
    }
    pub fn hash(data: &[u64], padding: bool) -> [u64; 4] {
        let mut hasher = Self::new();
        if padding {
            let group = data.len() / 3;
            let mut j = 0;
            for i in 0..group {
                j = i*3;
                hasher.update(data[j]);
                hasher.update(data[j+1]);
                hasher.update(data[j+2]);
                hasher.update(0u64);
            }
            j += 3;
            for i in j..data.len() {
                hasher.update(data[i]);
            }
        } else {
            for d in data {
                hasher.update(*d);
            }
        }
        hasher.finalize()
    }
    pub fn update(&mut self, v:u64) {
        unsafe {
            poseidon_push(v);
        }
        self.0 += 1;
        if self.0 == 32 {
            unsafe {
                poseidon_finalize();
                poseidon_finalize();
                poseidon_finalize();
                poseidon_finalize();
                poseidon_new(0u64);
            }
            self.0 = 0;
        }
    }
    pub fn finalize(&mut self) -> [u64; 4] {
        if (self.0 & 0x3) != 0 {
            for _ in (self.0 & 0x3) .. 4 {
                unsafe {
                    poseidon_push(0);
                }
                self.0 += 1;
            }
        }
        if self.0 == 32 {
            unsafe {
                poseidon_finalize();
                poseidon_finalize();
                poseidon_finalize();
                poseidon_finalize();
                poseidon_new(0u64);
            }
            self.0 = 0;
        }
        unsafe {
            poseidon_push(1);
        }
        self.0 += 1;
        for _ in self.0 .. 32 {
            unsafe {
                poseidon_push(0);
            }
        }
        unsafe {
            [
                poseidon_finalize(),
                poseidon_finalize(),
                poseidon_finalize(),
                poseidon_finalize(),
            ]
        }
    }
}