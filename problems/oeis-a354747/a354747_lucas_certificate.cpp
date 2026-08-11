#include <gmpxx.h>

#include <iostream>
#include <thread>

// Deterministic Lucas-rank certificate for
//     N = 201886*3^39101 - 1.
//
// Put A=N+1=2*100943*3^39101 and use the Lucas sequence
// U_n(P,Q) with (P,Q)=(8,5), whose discriminant is D=44.
// The computation below verifies
//
//   U_A == 0 (mod N),
//   gcd(U_(A/q),N) == 1 for q=2,3,100943.
//
// Hence, for every prime ell|N, the rank of apparition of ell is exactly
// A.  The standard Lucas rank theorem gives
// A | ell-(D/ell), so A<=ell+1.  As A=N+1, ell>=N and therefore ell=N.

namespace {

constexpr unsigned long exponent = 39101;
constexpr unsigned long large_factor = 100943;
constexpr long lucas_p = 8;
constexpr long lucas_q = 5;
constexpr long discriminant = 44;

void normalize(mpz_class& x, const mpz_class& modulus) {
    x %= modulus;
    if (x < 0) x += modulus;
}

void lucas_at(unsigned long index, const mpz_class& modulus,
              mpz_class& u, mpz_class& v, mpz_class& q_power) {
    u = 1;
    v = lucas_p;
    q_power = lucas_q;
    const mpz_class inverse_two = (modulus + 1) / 2;
    const int top_bit = 8 * sizeof(unsigned long) - 1 - __builtin_clzl(index);

    for (int bit = top_bit - 1; bit >= 0; --bit) {
        mpz_class u2 = u * v;
        normalize(u2, modulus);
        mpz_class v2 = v * v - 2 * q_power;
        normalize(v2, modulus);
        mpz_class q2 = q_power * q_power;
        normalize(q2, modulus);

        if ((index >> bit) & 1UL) {
            mpz_class next_u = (lucas_p * u2 + v2) * inverse_two;
            normalize(next_u, modulus);
            mpz_class next_v = (discriminant * u2 + lucas_p * v2) * inverse_two;
            normalize(next_v, modulus);
            u = std::move(next_u);
            v = std::move(next_v);
            q_power = q2 * lucas_q;
            normalize(q_power, modulus);
        } else {
            u = std::move(u2);
            v = std::move(v2);
            q_power = std::move(q2);
        }
    }
}

// For odd k:
// U_(3k)=U_k*(V_k^2-Q^k), V_(3k)=V_k*(V_k^2-3Q^k).
void triple_odd_index(mpz_class& u, mpz_class& v, mpz_class& q_power,
                      const mpz_class& modulus) {
    mpz_class v2 = v * v;
    normalize(v2, modulus);
    mpz_class next_u = u * (v2 - q_power);
    normalize(next_u, modulus);
    mpz_class next_v = v * (v2 - 3 * q_power);
    normalize(next_v, modulus);
    mpz_class next_q = q_power * q_power;
    normalize(next_q, modulus);
    next_q *= q_power;
    normalize(next_q, modulus);
    u = std::move(next_u);
    v = std::move(next_v);
    q_power = std::move(next_q);
}

mpz_class gcd_with(const mpz_class& x, const mpz_class& modulus) {
    mpz_class result;
    mpz_gcd(result.get_mpz_t(), x.get_mpz_t(), modulus.get_mpz_t());
    return result;
}

bool trial_prime(unsigned long n) {
    if (n < 2) return false;
    if (n % 2 == 0) return n == 2;
    for (unsigned long d = 3; d * d <= n; d += 2) {
        if (n % d == 0) return false;
    }
    return true;
}

struct MainBranch {
    mpz_class u_a;
    mpz_class gcd_half;
    mpz_class gcd_third;
};

struct CofactorBranch {
    mpz_class gcd_large_factor;
};

}  // namespace

int main() {
    mpz_class N;
    mpz_ui_pow_ui(N.get_mpz_t(), 3, exponent);
    N *= 201886;
    N -= 1;

    MainBranch main_branch;
    CofactorBranch cofactor_branch;

    std::thread first([&] {
        // Index large_factor*3^i; all these indices are odd.
        mpz_class u, v, q_power, previous_u, previous_v;
        lucas_at(large_factor, N, u, v, q_power);
        for (unsigned long i = 1; i <= exponent; ++i) {
            if (i == exponent) {
                previous_u = u;
                previous_v = v;
            }
            triple_odd_index(u, v, q_power, N);
        }
        // U_(2k)=U_k*V_k.
        main_branch.u_a = u * v;
        normalize(main_branch.u_a, N);
        main_branch.gcd_half = gcd_with(u, N);
        mpz_class u_a_over_three = previous_u * previous_v;
        normalize(u_a_over_three, N);
        main_branch.gcd_third = gcd_with(u_a_over_three, N);
    });

    std::thread second([&] {
        // Index 3^i, then double it to obtain A/large_factor.
        mpz_class u = 1;
        mpz_class v = lucas_p;
        mpz_class q_power = lucas_q;
        for (unsigned long i = 1; i <= exponent; ++i) {
            triple_odd_index(u, v, q_power, N);
        }
        mpz_class u_a_over_large_factor = u * v;
        normalize(u_a_over_large_factor, N);
        cofactor_branch.gcd_large_factor = gcd_with(u_a_over_large_factor, N);
    });

    first.join();
    second.join();

    const mpz_class parameter_gcd = gcd_with(mpz_class(2 * lucas_q * discriminant), N);
    const int jacobi = mpz_jacobi(mpz_class(discriminant).get_mpz_t(), N.get_mpz_t());
    const bool factor_is_prime = trial_prime(large_factor);

    std::cout << "N_bits=" << mpz_sizeinbase(N.get_mpz_t(), 2) << '\n';
    std::cout << "N_digits=" << mpz_sizeinbase(N.get_mpz_t(), 10) << '\n';
    std::cout << "N_plus_1_factorization=2*100943*3^39101\n";
    std::cout << "100943_trial_prime=" << factor_is_prime << '\n';
    std::cout << "gcd(2*Q*D,N)=" << parameter_gcd << '\n';
    std::cout << "jacobi(D,N)=" << jacobi << '\n';
    std::cout << "U_A_mod_N=" << main_branch.u_a << '\n';
    std::cout << "gcd(U_(A/2),N)=" << main_branch.gcd_half << '\n';
    std::cout << "gcd(U_(A/3),N)=" << main_branch.gcd_third << '\n';
    std::cout << "gcd(U_(A/100943),N)="
              << cofactor_branch.gcd_large_factor << '\n';

    const bool ok = factor_is_prime && parameter_gcd == 1 && jacobi == -1 &&
                    main_branch.u_a == 0 && main_branch.gcd_half == 1 &&
                    main_branch.gcd_third == 1 &&
                    cofactor_branch.gcd_large_factor == 1;
    std::cout << (ok ? "LUCAS_RANK_CERTIFICATE_OK" : "CERTIFICATE_FAILED") << '\n';
    return ok ? 0 : 1;
}
