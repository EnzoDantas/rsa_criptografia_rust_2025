// Implementação Didática de Criptografia RSA em Rust
// Projeto Acadêmico - 2025

use num_bigint::{BigUint, RandBigInt};
use num_traits::{One, Zero};
use rand::thread_rng;

/// Calcula o MDC (Máximo Divisor Comum) usando o algoritmo de Euclides
/// Este é usado para verificar se dois números são coprimos
fn mdc(mut a: BigUint, mut b: BigUint) -> BigUint {
    while !b.is_zero() {
        let temp = b.clone();
        b = a % &b;
        a = temp;
    }
    a
}

/// Algoritmo de Euclides Estendido
/// Retorna (mdc, x, y) onde mdc = a*x + b*y
fn euclides_estendido(a: &BigUint, b: &BigUint) -> (BigUint, BigUint, BigUint) {
    if b.is_zero() {
        return (a.clone(), One::one(), Zero::zero());
    }
    
    let (mdc, x1, y1) = euclides_estendido(b, &(a % b));
    let x = y1.clone();
    let y = if x1 >= (a / b) * &y1 {
        x1 - (a / b) * y1
    } else {
        x1 + b - (a / b) * y1
    };
    
    (mdc, x, y)
}

/// Calcula o inverso modular de 'a' módulo 'm'
/// Retorna Some(inverso) se existir, None caso contrário
fn inverso_modular(a: &BigUint, m: &BigUint) -> Option<BigUint> {
    let (mdc, x, _) = euclides_estendido(a, m);
    
    if !mdc.is_one() {
        return None; // Inverso não existe
    }
    
    // Garante que o resultado seja positivo
    Some(x % m)
}

/// Exponenciação modular eficiente (a^b mod m)
/// Usa o método de exponenciação binária para eficiência
fn exp_modular(base: &BigUint, exp: &BigUint, modulo: &BigUint) -> BigUint {
    let mut resultado: BigUint = One::one();
    let mut base = base % modulo;
    let mut exp = exp.clone();
    
    while !exp.is_zero() {
        // Se o bit menos significativo é 1
        if (&exp & BigUint::one()) == BigUint::one() {
            resultado = (resultado * &base) % modulo;
        }
        
        // Desloca o expoente para a direita (divisão por 2)
        exp = exp >> 1;
        // Eleva a base ao quadrado
        base = (&base * &base) % modulo;
    }
    
    resultado
}

/// Teste de primalidade de Miller-Rabin
/// Retorna true se n provavelmente é primo, false se é composto
fn teste_miller_rabin(n: &BigUint, k: usize) -> bool {
    if n <= &BigUint::one() {
        return false;
    }
    if n == &BigUint::from(2u32) || n == &BigUint::from(3u32) {
        return true;
    }
    if (n & BigUint::one()).is_zero() {
        return false; // Número par
    }
    
    // Escreve n-1 como 2^r * d
    let mut d = n - BigUint::one();
    let mut r = 0u32;
    while (&d & BigUint::one()).is_zero() {
        d = d >> 1;
        r += 1;
    }
    
    let mut rng = thread_rng();
    
    // Realiza k rodadas do teste
    'outer: for _ in 0..k {
        let a = rng.gen_biguint_range(&BigUint::from(2u32), &(n - BigUint::from(2u32)));
        let mut x = exp_modular(&a, &d, n);
        
        if x == BigUint::one() || x == n - BigUint::one() {
            continue;
        }
        
        for _ in 0..(r - 1) {
            x = exp_modular(&x, &BigUint::from(2u32), n);
            if x == n - BigUint::one() {
                continue 'outer;
            }
        }
        
        return false; // n é composto
    }
    
    true // n é provavelmente primo
}

/// Gera um número primo aleatório com o número especificado de bits
fn gerar_primo(bits: usize) -> BigUint {
    let mut rng = thread_rng();
    
    loop {
        // Gera um número aleatório com 'bits' bits
        let mut candidato = rng.gen_biguint(bits as u64);
        
        // Garante que o bit mais significativo está definido
        candidato |= BigUint::one() << (bits - 1);
        // Garante que é ímpar
        candidato |= BigUint::one();
        
        // Testa se é primo
        if teste_miller_rabin(&candidato, 20) {
            return candidato;
        }
    }
}

/// Estrutura que representa um par de chaves RSA
#[derive(Debug, Clone)]
struct ChavesRSA {
    /// Chave pública (e, n)
    pub chave_publica: (BigUint, BigUint),
    /// Chave privada (d, n)
    pub chave_privada: (BigUint, BigUint),
}

impl ChavesRSA {
    /// Gera um novo par de chaves RSA com o tamanho especificado
    fn gerar(bits: usize) -> Self {
        println!("Gerando números primos...\n");
        
        // Passo 1: Gerar dois números primos grandes p e q
        let p = gerar_primo(bits / 2);
        println!("Primo p gerado: {} bits", p.bits());
        
        let q = gerar_primo(bits / 2);
        println!("Primo q gerado: {} bits\n", q.bits());
        
        // Passo 2: Calcular n = p * q (módulo)
        let n = &p * &q;
        println!("Módulo n = p * q");
        println!("Tamanho de n: {} bits\n", n.bits());
        
        // Passo 3: Calcular φ(n) = (p-1) * (q-1) (função totiente de Euler)
        let phi = (&p - BigUint::one()) * (&q - BigUint::one());
        println!("Calculando φ(n) = (p-1) * (q-1)\n");
        
        // Passo 4: Escolher e tal que 1 < e < φ(n) e mdc(e, φ(n)) = 1
        // Comumente usa-se e = 65537 (2^16 + 1) por ser primo e eficiente
        let e = BigUint::from(65537u32);
        println!("Expoente público e: {}\n", e);
        
        // Verifica se e e φ(n) são coprimos
        assert_eq!(mdc(e.clone(), phi.clone()), BigUint::one(), "e e φ(n) devem ser coprimos");
        
        // Passo 5: Calcular d tal que d * e ≡ 1 (mod φ(n))
        // d é o inverso modular de e módulo φ(n)
        let d = inverso_modular(&e, &phi).expect("Falha ao calcular inverso modular");
        println!("Expoente privado d calculado\n");
        
        // Verificação: d * e mod φ(n) deve ser 1
        assert_eq!((&d * &e) % &phi, BigUint::one());
        
        ChavesRSA {
            chave_publica: (e, n.clone()),
            chave_privada: (d, n),
        }
    }
    
    /// Criptografa uma mensagem usando a chave pública
    fn criptografar(&self, mensagem: &BigUint) -> BigUint {
        let (e, n) = &self.chave_publica;
        
        // Verifica se a mensagem é menor que n
        assert!(mensagem < n, "Mensagem deve ser menor que n");
        
        // Calcula: texto_cifrado = mensagem^e mod n
        exp_modular(mensagem, e, n)
    }
    
    /// Descriptografa um texto cifrado usando a chave privada
    fn descriptografar(&self, texto_cifrado: &BigUint) -> BigUint {
        let (d, n) = &self.chave_privada;
        
        // Calcula: mensagem = texto_cifrado^d mod n
        exp_modular(texto_cifrado, d, n)
    }
}

fn main() {
    println!("=".repeat(60));
    println!("   DEMONSTRAÇÃO DE CRIPTOGRAFIA RSA EM RUST");
    println!("   Implementação Didática - Projeto Acadêmico 2025");
    println!("=".repeat(60));
    println!();
    
    // Tamanho da chave em bits (512 bits é pequeno para fins didáticos)
    // Em produção, deve-se usar pelo menos 2048 bits
    let tamanho_chave = 512;
    
    println!("1. GERAÇÃO DE CHAVES RSA");
    println!("-".repeat(60));
    println!("Tamanho da chave: {} bits\n", tamanho_chave);
    
    let chaves = ChavesRSA::gerar(tamanho_chave);
    
    let (e, n) = &chaves.chave_publica;
    println!("Chave Pública (e, n):");
    println!("  e: {}", e);
    println!("  n: {}...{} ({} bits)\n", 
             &n.to_string()[..20], 
             &n.to_string()[n.to_string().len()-10..],
             n.bits());
    
    println!();
    println!("2. CRIPTOGRAFIA E DESCRIPTOGRAFIA");
    println!("-".repeat(60));
    
    // Mensagem de exemplo (como número)
    // Em uma implementação real, texto seria convertido para números
    let mensagem_original = BigUint::from(123456789u32);
    println!("Mensagem original: {}\n", mensagem_original);
    
    // Criptografa
    println!("Criptografando mensagem...");
    let texto_cifrado = chaves.criptografar(&mensagem_original);
    println!("Texto cifrado: {}\n", texto_cifrado);
    
    // Descriptografa
    println!("Descriptografando mensagem...");
    let mensagem_recuperada = chaves.descriptografar(&texto_cifrado);
    println!("Mensagem recuperada: {}\n", mensagem_recuperada);
    
    // Verificação
    println!();
    println!("3. VERIFICAÇÃO");
    println!("-".repeat(60));
    if mensagem_original == mensagem_recuperada {
        println!("✓ SUCESSO: Mensagem recuperada corretamente!");
        println!("  Original:   {}", mensagem_original);
        println!("  Recuperada: {}", mensagem_recuperada);
    } else {
        println!("✗ ERRO: Mensagem não foi recuperada corretamente!");
    }
    
    println!();
    println!("=".repeat(60));
    println!("Demonstração concluída com sucesso!");
    println!("=".repeat(60));
}
