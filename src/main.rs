use num_bigint::BigUint;
use num_integer::Integer; // para gcd
use num_traits::{One, Zero};
use rand::Rng; // rand 0.9
use std::ops::{Add, Mul, Sub};

// Utilitários para BigUint
fn biguint_from_u64(n: u64) -> BigUint {
    BigUint::from(n)
}

// Gera BigUint "aleatório" com 'bits' bits usando rand em blocos de u32
fn random_biguint(bits: usize, rng: &mut impl Rng) -> BigUint {
    if bits == 0 {
        return BigUint::zero();
    }
    let words = (bits + 31) / 32; // quantidade de u32
    let mut acc = BigUint::zero();
    for i in 0..words {
        let mut w = rng.random::<u32>() as u64;
        // Na palavra mais alta, limita os bits excedentes para atingir exatamente 'bits'
        if i == words - 1 {
            let extra = words * 32 - bits;
            if extra > 0 {
                w &= (1u64 << (32 - extra)) - 1;
            }
            // Garante bit alto para não devolver número pequeno demais
            if bits > 1 {
                w |= 1u64 << (31 - extra);
            }
        }
        acc = (acc << 32) + BigUint::from(w);
    }
    acc
}

// Gera número ímpar > 2 com 'bits' bits
fn random_odd_biguint(bits: usize, rng: &mut impl Rng) -> BigUint {
    let mut n = random_biguint(bits, rng);
    if n <= BigUint::from(2u32) {
        n = BigUint::from(3u32);
    }
    if n.is_even() {
        n += BigUint::one();
    }
    n
}

// Teste de primalidade simples (Miller-Rabin determinístico para tamanhos pequenos)
// Para simplicidade no Playground, fazemos um teste probabilístico leve.
fn is_probable_prime(n: &BigUint, k: usize, rng: &mut impl Rng) -> bool {
    if n <= &BigUint::from(3u32) {
        return *n == BigUint::from(2u32) || *n == BigUint::from(3u32);
    }
    if n.is_even() {
        return false;
    }
    // escreve n-1 = d * 2^r
    let one = BigUint::one();
    let two = biguint_from_u64(2);
    let mut d = n - &one;
    let mut r = 0u32;
    while (&d & (&two - &one)).is_zero() { // enquanto d % 2 == 0
        d >>= 1usize;
        r += 1;
    }
    'witness_loop: for _ in 0..k {
        // escolhe a em [2, n-2]
        // cria a a partir de bits de n, mas limita ao intervalo
        let mut a = random_biguint(n.bits() as usize, rng);
        if &a < &two {
            a = two.clone();
        }
        if &a >= &(n - &two) {
            a = n - &two;
        }
        let mut x = a.modpow(&d, n);
        if x == one || x == n - &one {
            continue 'witness_loop;
        }
        for _ in 1..r {
            x = x.modpow(&two, n);
            if x == n - &one {
                continue 'witness_loop;
            }
        }
        return false;
    }
    true
}

// Gera provável primo com 'bits' bits
fn gen_prime(bits: usize, rng: &mut impl Rng) -> BigUint {
    loop {
        let candidate = random_odd_biguint(bits, rng);
        if is_probable_prime(&candidate, 10, rng) {
            return candidate;
        }
    }
}

// RSA mínimo para demonstração
#[derive(Clone)]
struct ChavesRSA {
    n: BigUint,
    e: BigUint,
    d: BigUint,
}

impl ChavesRSA {
    fn gerar(bits: usize) -> Self {
        let mut rng = rand::rng();
        let half = bits / 2;
        let p = gen_prime(half, &mut rng);
        let q = gen_prime(bits - half, &mut rng);
        let n = &p * &q;
        let one = BigUint::one();
        let phi = (p - &one) * (q - &one);
        // escolhe e pequeno comum
        let e_candidates = [3u32, 5, 17, 257, 65537];
        let mut e = BigUint::from(65537u32);
        for &cand in &e_candidates {
            let ee = BigUint::from(cand);
            if ee.gcd(&phi).is_one() {
                e = ee;
                break;
            }
        }
        let d = modinv(&e, &phi).expect("e e phi coprimos");
        Self { n, e, d }
    }

    fn criptografar(&self, msg: &str) -> BigUint {
        let m = BigUint::from_bytes_be(msg.as_bytes());
        m.modpow(&self.e, &self.n)
    }

    fn descriptografar(&self, c: &BigUint) -> String {
        let m = c.modpow(&self.d, &self.n);
        let bytes = m.to_bytes_be();
        String::from_utf8(bytes).unwrap_or_else(|_| "<bytes não UTF-8>".to_string())
    }
}

// Inverso modular usando estendido sobre inteiros assinados de big-int via num-bigint::BigUint + i128 fallback
fn egcd(a: BigUint, b: BigUint) -> (BigUint, BigIntLike, BigIntLike) {
    // Implementação simples usando i128 para pequenos 'a', mas para generalidade completa seria BigInt.
    // Para manter dependências baixas no Playground, implementamos versão sobre BigUint retornando coeficientes positivos.
    if b.is_zero() {
        return (a, BigIntLike::one(), BigIntLike::zero());
    }
    let (g, x1, y1) = egcd(b.clone(), a.clone() % b.clone());
    // x = y1, y = x1 - (a/b) * y1
    let q = a / b;
    let x = y1.clone();
    let y = x1 - q * y1;
    (g, x, y)
}

// Um tipo inteiro assinado mínimo com magnitude BigUint para suportar egcd
#[derive(Clone, Debug)]
struct BigIntLike {
    neg: bool,
    mag: BigUint,
}

impl BigIntLike {
    fn zero() -> Self { Self { neg: false, mag: BigUint::zero() } }
    fn one() -> Self { Self { neg: false, mag: BigUint::one() } }
}

use std::ops::{Div, Rem, Shl};

impl Mul<BigIntLike> for BigUint {
    type Output = BigIntLike;
    fn mul(self, rhs: BigIntLike) -> BigIntLike {
        BigIntLike { neg: rhs.neg, mag: self * rhs.mag }
    }
}

impl Sub<BigIntLike> for BigIntLike {
    type Output = BigIntLike;
    fn sub(self, rhs: BigIntLike) -> BigIntLike {
        match (self.neg, rhs.neg) {
            (false, false) => {
                if self.mag >= rhs.mag {
                    BigIntLike { neg: false, mag: self.mag - rhs.mag }
                } else {
                    BigIntLike { neg: true, mag: rhs.mag - self.mag }
                }
            }
            (true, true) => {
                // (-a) - (-b) = -(a - b)
                BigIntLike { neg: !(self.mag >= rhs.mag), mag: if self.mag >= rhs.mag { self.mag - rhs.mag } else { rhs.mag - self.mag } }
            }
            (false, true) => BigIntLike { neg: false, mag: self.mag + rhs.mag },
            (true, false) => BigIntLike { neg: true, mag: self.mag + rhs.mag },
        }
    }
}

impl Mul<BigUint> for BigIntLike {
    type Output = BigIntLike;
    fn mul(self, rhs: BigUint) -> BigIntLike {
        BigIntLike { neg: self.neg, mag: self.mag * rhs }
    }
}

impl Add<BigIntLike> for BigIntLike {
    type Output = BigIntLike;
    fn add(self, rhs: BigIntLike) -> BigIntLike {
        match (self.neg, rhs.neg) {
            (false, false) => BigIntLike { neg: false, mag: self.mag + rhs.mag },
            (true, true) => BigIntLike { neg: true, mag: self.mag + rhs.mag },
            (false, true) => {
                if self.mag >= rhs.mag { BigIntLike { neg: false, mag: self.mag - rhs.mag } } else { BigIntLike { neg: true, mag: rhs.mag - self.mag } }
            }
            (true, false) => {
                if rhs.mag >= self.mag { BigIntLike { neg: false, mag: rhs.mag - self.mag } } else { BigIntLike { neg: true, mag: self.mag - rhs.mag } }
            }
        }
    }
}

impl Mul<BigIntLike> for BigIntLike {
    type Output = BigIntLike;
    fn mul(self, rhs: BigIntLike) -> BigIntLike {
        BigIntLike { neg: self.neg ^ rhs.neg, mag: self.mag * rhs.mag }
    }
}

impl From<BigUint> for BigIntLike {
    fn from(v: BigUint) -> Self { BigIntLike { neg: false, mag: v } }
}

fn modinv(a: &BigUint, m: &BigUint) -> Option<BigUint> {
    // Usa algoritmo estendido trabalhando apenas com BigUint via simulação de sinal
    // Esta implementação é simplificada e suficiente para e pequeno e m grande.
    let mut t = BigIntLike::zero();
    let mut new_t = BigIntLike::one();
    let mut r = m.clone();
    let mut new_r = a.clone();
    while !new_r.is_zero() {
        let q = &r / &new_r;
        // (t, new_t) = (new_t, t - q*new_t)
        let tmp_t = new_t.clone();
        new_t = t.clone() - BigIntLike { neg: false, mag: q.clone() } * new_t;
        t = tmp_t;
        // (r, new_r) = (new_r, r - q*new_r)
        let tmp_r = new_r.clone();
        new_r = r - &q * &tmp_r;
        r = tmp_r;
    }
    if r != BigUint::one() {
        return None; // não inversível
    }
    // garante positivo: if t < 0 { t += m }
    let mut t_mag = t.mag;
    if t.neg { t_mag = (t_mag % m) + m; }
    Some(t_mag % m)
}

fn main() {
    // 1. Gera chaves
    println!("1. GERAÇÃO DE CHAVES");
    println!("{}", "=".repeat(60));
    let chaves = ChavesRSA::gerar(128); // bits pequenos para Playground
    println!("n (modulus) = {}", chaves.n);
    println!("e (public)  = {}", chaves.e);
    println!("{}", "=".repeat(60));

    // 2. Criptografa
    let mensagem_original = "Olá, mundo criptografado!";
    println!("2. CRIPTOGRAFIA");
    println!("{}", "-".repeat(60));
    println!("Criptografando mensagem...");
    let texto_cifrado = chaves.criptografar(&mensagem_original);
    println!("Texto cifrado: {}\n", texto_cifrado);

    // 3. Descriptografa
    println!("Descriptografando mensagem...");
    let mensagem_recuperada = chaves.descriptografar(&texto_cifrado);
    println!("Mensagem recuperada: {}\n", mensagem_recuperada);

    // 4. Verificação
    println!("3. VERIFICAÇÃO");
    println!("{}", "-".repeat(60));
    if mensagem_original == mensagem_recuperada {
        println!("OK: mensagem original foi recuperada.");
    } else {
        println!("FALHA: mensagens diferem.");
    }
    println!("{}", "=".repeat(60));
}
