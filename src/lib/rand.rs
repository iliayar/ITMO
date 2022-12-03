use aes::cipher::{generic_array::GenericArray, BlockCipher, BlockEncrypt, KeyInit};

const KEY_SIZE: usize = BLOCK_SIZE * 2;
const BLOCK_SIZE: usize = 16;

type Num = usize;
const NUM_SIZE: usize = std::mem::size_of::<Num>();

type SeedNum = u64;

pub struct Rand {
    key: [u8; KEY_SIZE],
    min: Num,
    max: Num,
}

impl Rand {
    pub fn new(seed: SeedNum, min: Num, max: Num) -> Self {
        let mut key_raw = seed.to_be_bytes().to_vec();
        key_raw.resize(KEY_SIZE, 0);
        let key = clone_slice(&key_raw);
        Self { key, min, max }
    }

    pub fn get(&self, data: &str) -> Num {
        let mut data_bytes = data.as_bytes().to_vec();
        let nblocks = (data_bytes.len() + BLOCK_SIZE - 1) / BLOCK_SIZE;
        data_bytes.resize(nblocks * BLOCK_SIZE, 0);

        let mut blocks: Vec<_> = data_bytes
            .chunks(BLOCK_SIZE)
            .map(|chunk| GenericArray::from(clone_slice::<u8, BLOCK_SIZE>(chunk)))
            .collect();

        let key = GenericArray::from(self.key);
        let cipher = aes::Aes256::new(&key);

        let mut res: Num = 0;
        for block in blocks.iter_mut() {
            cipher.encrypt_block(block);
            let bytes = clone_slice::<u8, NUM_SIZE>(&block[0..NUM_SIZE]);
            res ^= Num::from_be_bytes(bytes);
        }

        return res % self.max + self.min;
    }
}

fn clone_slice<T: Copy + Default, const N: usize>(slice: &[T]) -> [T; N] {
    assert!(N == slice.len());
    let mut res: [T; N] = [T::default(); N];
    for (i, n) in slice.iter().enumerate() {
        res[i] = *n;
    }

    return res;
}
