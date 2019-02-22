import data.nat.prime

open nat

lemma larger_prime' : ∀ n : ℕ, ∃ p, (prime p) ∧ (p > n) := 
begin
 intro n,
 let m := fact n + 1,
 let p := min_fac m,
 have m_ne_1 : m ≠ 1 := ne_of_gt (nat.succ_lt_succ (fact_pos n)),
 have p_gt_0 : p > 0 := min_fac_pos m,
 have p_prime : prime p := min_fac_prime m_ne_1,
 have not_p_le_n : ¬ p ≤ n, {
  intro p_le_n,
  have d0 : p ∣ fact n := dvd_fact p_gt_0 p_le_n,
  have d1 : p ∣ fact n + 1 := min_fac_dvd m,
  have d  : p ∣ 1 := (nat.dvd_add_iff_right d0).mpr d1,
  exact prime.not_dvd_one p_prime d
 },
 have p_gt_n : p > n := lt_of_not_ge not_p_le_n,
 exact ⟨p,⟨p_prime,p_gt_n⟩⟩,
end

lemma larger_prime'' : ∀ n : ℕ, ∃ p, (prime p) ∧ (p > n) := 
λ n, 
 let m := fact n + 1 in
 let p := min_fac m in 
 let p_prime := min_fac_prime (ne_of_gt (nat.succ_lt_succ (fact_pos n))) in
  ⟨p,⟨p_prime,
          (lt_of_not_ge (λ p_le_n,
                         prime.not_dvd_one
                         p_prime ((nat.dvd_add_iff_right
                                    (dvd_fact p_prime.pos p_le_n)).mpr (min_fac_dvd m))))⟩⟩


