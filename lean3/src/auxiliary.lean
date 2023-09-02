import tactic
import data.zmod.basic
import data.nat.squarefree

/-!
### Useful lemmas
-/

lemma squarefree.neg {R} [monoid R] [has_distrib_neg R] {r : R} (h : squarefree r) :
  squarefree (-r) :=
λ x hx, h x (dvd_neg.mp hx)

namespace int

-- The `nat` version of this exists.
lemma mul_div_le {m : ℤ} (h : 0 < m) (n : ℤ) : m * (n / m) ≤ n :=
begin
  nth_rewrite 1 ← div_add_mod n m,
  simp only [mod_nonneg n h.ne', le_add_iff_nonneg_right],
end

-- compare `nat.exists_coprime` and `nat.exists.coprime'`
lemma make_primitive (a b : ℤ) :
  ∃ g a₁ b₁ : ℤ, g = a.gcd b ∧ a = g * a₁ ∧ b = g * b₁ ∧  a₁.gcd b₁ = 1 :=
begin
  by_cases h : a = 0 ∧ b = 0,
  { refine ⟨0, 1, 1, _⟩,
    simp only [h.1, h.2, gcd_zero_right, zmod.nat_cast_self, eq_self_iff_true, zero_mul,
               gcd_one_right, and_self], },
  { rw [not_and_distrib, ← ne.def, ← ne.def] at h,
    have hg := gcd_pos_iff.mpr h,
    have hg' := (nat.cast_pos.mpr hg).ne',
    refine ⟨a.gcd b, a / a.gcd b, b / a.gcd b, rfl, _, _, _⟩,
    { rw ← int.mul_div_assoc _ (gcd_dvd_left _ _),
      exact (int.mul_div_cancel_left _ hg').symm, },
    { rw ← int.mul_div_assoc _ (gcd_dvd_right _ _),
      exact (int.mul_div_cancel_left _ hg').symm, },
    { exact gcd_div_gcd_div_gcd hg, },
    { apply_instance, } }
end

lemma make_primitive_3 (a b c : ℤ) :
  ∃ g a₁ b₁ c₁ : ℤ, g = a.gcd (b.gcd c) ∧ a = g * a₁ ∧ b = g * b₁ ∧ c = g * c₁ ∧
                    a₁.gcd (b₁.gcd c₁) = 1 :=
begin
  obtain ⟨g₁, b₂, c₂, hg₁, hgb, hgc, hg₁'⟩ := make_primitive b c,
  obtain ⟨g, a₁, w, hg, hga, hgw, hg'⟩ := make_primitive a g₁,
  cases eq_or_ne g 0 with hg₀ hg₀,
  { rw [hg₀, zero_mul] at *,
    rw ← hg₁ at *,
    rw [hgw, zero_mul] at *,
    refine ⟨0, 1, 1, 1, hg, by rwa zero_mul, by rwa zero_mul, by rwa zero_mul, _⟩,
    simp only [gcd_one_right, algebra_map.coe_one], },
  { have hw₁ : 0 ≤ w,
    { have hg₁₀ : 0 ≤ g₁ := by { rw hg₁, exact nat.cast_nonneg _, },
      replace hg₀ : 0 < g,
      { have : 0 ≤ g := by { rw hg, exact nat.cast_nonneg _, },
        exact (eq_or_lt_of_le this).resolve_left hg₀.symm, },
      contrapose! hg₁₀,
      rw hgw,
      exact mul_neg_iff.mpr (or.inl ⟨hg₀, hg₁₀⟩), },
    refine ⟨g, a₁, w * b₂, w * c₂, by rwa hg₁ at hg, 
            hga, by rw [hgb, hgw, mul_assoc], by rw [hgc, hgw, mul_assoc], _⟩,
    convert hg',
    rw [gcd_mul_left, hg₁', mul_one, coe_nat_abs, abs_of_nonneg hw₁], }
end

-- The `nat` and `gcd_monoid` versions of this exist.
lemma dvd_gcd_iff {k: ℕ} {m n : ℤ} : k ∣ m.gcd n ↔ ↑k ∣ m ∧ ↑k ∣ n :=
begin
  rw [gcd_eq_nat_abs, coe_nat_dvd_left, coe_nat_dvd_left],
  exact nat.dvd_gcd_iff,
end

lemma not_is_coprime_iff_exists_prime_dvd {a b : ℤ} :
  ¬ is_coprime a b ↔ ∃ p : ℕ, p.prime ∧ ↑p ∣ a ∧ ↑p ∣ b :=
begin
  rw [← gcd_eq_one_iff_coprime, nat.eq_one_iff_not_exists_prime_dvd],
  push_neg,
  simp_rw [dvd_gcd_iff],
end

lemma not_is_coprime_of_mul_prime {p : ℕ} (hp : p.prime) (a b : ℤ) :
  ¬ is_coprime (↑p * a) (↑p * b) :=
not_is_coprime_iff_exists_prime_dvd.mpr ⟨p, hp, dvd_mul_right _ _, dvd_mul_right _ _⟩

lemma squarefree_iff_squarefree_nat_abs {n : ℤ} : squarefree n ↔ squarefree n.nat_abs :=
begin
  refine ⟨λ h x hx, _, λ h x hx, _⟩,
  { have : (x * x : ℤ) ∣ n.nat_abs := by exact_mod_cast hx,
    exact of_nat_is_unit.mp (h (↑x) (dvd_nat_abs.mp this)), },
  { rw [← nat_abs_dvd_iff_dvd, nat_abs_mul] at hx,
    exact is_unit_iff_nat_abs_eq.mpr (nat.is_unit_iff.mp $ h x.nat_abs hx), }
end

lemma is_coprime_abs {m n : ℤ} :
  is_coprime m n ↔ is_coprime (|m|) (|n|) :=
begin
  cases abs_choice m with hm hm; cases abs_choice n with hn hn; rw [hm, hn],
  { exact (is_coprime.neg_right_iff m n).symm, },
  { exact (is_coprime.neg_left_iff m n).symm, },
  { exact (is_coprime.neg_neg_iff m n).symm, }
end

lemma is_coprime_iff_coprime_nat_abs {m n : ℤ} :
  is_coprime m n ↔ nat.coprime m.nat_abs n.nat_abs :=
by rw [is_coprime_abs, abs_eq_nat_abs, abs_eq_nat_abs, nat.is_coprime_iff_coprime]

-- The `nat` version of this exists.
lemma squarefree_mul {m n : ℤ} (hmn : is_coprime m n) :
  squarefree (m * n) ↔ squarefree m ∧ squarefree n :=
begin
  simp_rw [squarefree_iff_squarefree_nat_abs, nat_abs_mul],
  exact nat.squarefree_mul (is_coprime_iff_coprime_nat_abs.mp hmn),
end

-- example (a : ℕ) : squarefree a ↔ squarefree (a : ℤ) := squarefree_coe_nat.symm

lemma is_coprime_of_squarefree_mul {a b : ℤ} (h : squarefree (a * b)) : is_coprime a b :=
begin
  by_contra hf,
  obtain ⟨p, hp, ⟨a',  ha⟩, ⟨b', hb⟩⟩ := not_is_coprime_iff_exists_prime_dvd.mp hf,
  have hd : ↑(p * p) ∣ a * b := ⟨a' * b', by {rw [ha, hb], push_cast, ring}⟩,
  exact hp.not_unit (of_nat_is_unit.mp $ h p hd),
end

-- The `nat` version of this exists.
lemma sq_mul_squarefree (n : ℤ) : ∃ (a b : ℤ), b ^ 2 * a = n ∧ squarefree a :=
begin
  obtain ⟨a', b', h, hs⟩ := nat.sq_mul_squarefree n.nat_abs,
  cases nat_abs_eq n with hn hn,
  { exact ⟨a', b', by {rw hn, exact_mod_cast h}, squarefree_coe_nat.mpr hs⟩, },
  { exact ⟨-a', b', by {rw [hn, ← h], push_cast, ring}, (squarefree_coe_nat.mpr hs).neg⟩, }
end

end int
