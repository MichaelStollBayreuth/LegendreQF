import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Squarefree

/-!
### Useful lemmas
-/


theorem Squarefree.neg {R} [Monoid R] [HasDistribNeg R] {r : R} (h : Squarefree r) :
    Squarefree (-r) := fun x hx => h x (dvd_neg.mp hx)

namespace Int

-- The `Nat` version of this exists: `Nat.mul_div_le`.
theorem mul_ediv_le {m : ℤ} (h : 0 < m) (n : ℤ) : m * (n / m) ≤ n := by
  nth_rw 2 [← ediv_add_emod n m]
  simp only [emod_nonneg _ h.ne', le_add_iff_nonneg_right]

-- compare `Nat.exists_coprime` and `Nat.exists_coprime'`
theorem make_primitive (a b : ℤ) :
    ∃ g a₁ b₁ : ℤ, g = a.gcd b ∧ a = g * a₁ ∧ b = g * b₁ ∧ a₁.gcd b₁ = 1 := by
  by_cases h : a = 0 ∧ b = 0
  · refine' ⟨0, 1, 1, _⟩
    simp only [h.1, h.2, gcd_zero_right, ZMod.nat_cast_self, eq_self_iff_true,
      MulZeroClass.zero_mul, gcd_one_right, and_self_iff]
  · rw [not_and_or, ← Ne.def, ← Ne.def] at h
    have hg := gcd_pos_iff.mpr h
    have hg' : (gcd a b : ℤ) ≠ 0 := coe_nat_ne_zero_iff_pos.mpr hg
    refine' ⟨a.gcd b, a / a.gcd b, b / a.gcd b, rfl, _, _, _⟩
    · rw [← Int.mul_ediv_assoc _ (gcd_dvd_left _ _)]
      exact (Int.mul_ediv_cancel_left _ hg').symm
    · rw [← Int.mul_ediv_assoc _ (gcd_dvd_right _ _)]
      exact (Int.mul_ediv_cancel_left _ hg').symm
    · exact gcd_div_gcd_div_gcd hg

theorem make_primitive_3 (a b c : ℤ) :
    ∃ g a₁ b₁ c₁ : ℤ,
      g = a.gcd (b.gcd c) ∧ a = g * a₁ ∧ b = g * b₁ ∧ c = g * c₁ ∧ a₁.gcd (b₁.gcd c₁) = 1 := by
  obtain ⟨g₁, b₂, c₂, hg₁, hgb, hgc, hg₁'⟩ := make_primitive b c
  obtain ⟨g, a₁, w, hg, hga, hgw, hg'⟩ := make_primitive a g₁
  cases' eq_or_ne g 0 with hg₀ hg₀
  · rw [hg₀] at hg hga hgw
    rw [zero_mul] at hga hgw
    rw [← hg₁]
    rw [hgw] at hg₁ hgb hgc hg ⊢
    rw [zero_mul] at hgb hgc
    refine'
      ⟨0, 1, 1, 1, hg, by rwa [zero_mul], by rwa [zero_mul], by rwa [zero_mul], _⟩
    simp only [gcd_one_right, algebraMap.coe_one]
  · have hw₁ : 0 ≤ w :=
      by
      have hg₁₀ : 0 ≤ g₁ := by rw [hg₁]; exact Nat.cast_nonneg _
      replace hg₀ : 0 < g
      · have : 0 ≤ g := by rw [hg]; exact Nat.cast_nonneg _
        exact (eq_or_lt_of_le this).resolve_left hg₀.symm
      contrapose! hg₁₀
      rw [hgw]
      exact mul_neg_iff.mpr (Or.inl ⟨hg₀, hg₁₀⟩)
    refine'
      ⟨g, a₁, w * b₂, w * c₂, by rwa [hg₁] at hg , hga, by rw [hgb, hgw, mul_assoc], by
        rw [hgc, hgw, mul_assoc], _⟩
    convert hg'
    simp only [gcd_mul_left, hg₁', mul_one, coe_natAbs, abs_eq_self, hw₁]

-- The `Nat` and `gcd_monoid` versions of this exist: `Nat.dvd_gcd_iff`, `dvd_gcd_iff`.
theorem dvd_gcd_iff {k : ℕ} {m n : ℤ} : k ∣ m.gcd n ↔ ↑k ∣ m ∧ ↑k ∣ n := by
  rw [gcd_eq_natAbs, coe_nat_dvd_left, coe_nat_dvd_left]
  exact Nat.dvd_gcd_iff

theorem not_isCoprime_iff_exists_prime_dvd {a b : ℤ} :
    ¬IsCoprime a b ↔ ∃ p : ℕ, p.Prime ∧ ↑p ∣ a ∧ ↑p ∣ b := by
  rw [← gcd_eq_one_iff_coprime, Nat.eq_one_iff_not_exists_prime_dvd]
  push_neg
  simp_rw [dvd_gcd_iff]

theorem not_isCoprime_of_mul_prime {p : ℕ} (hp : p.Prime) (a b : ℤ) :
    ¬IsCoprime (↑p * a) (↑p * b) :=
  not_isCoprime_iff_exists_prime_dvd.mpr ⟨p, hp, dvd_mul_right _ _, dvd_mul_right _ _⟩

theorem squarefree_iff_squarefree_natAbs {n : ℤ} : Squarefree n ↔ Squarefree n.natAbs := by
  refine' ⟨fun h x hx => _, fun h x hx => _⟩
  · have : (x * x : ℤ) ∣ n.natAbs := by exact_mod_cast hx
    exact ofNat_isUnit.mp (h (↑x) (dvd_natAbs.mp this))
  · rw [← natAbs_dvd_natAbs, natAbs_mul] at hx
    exact isUnit_iff_natAbs_eq.mpr (Nat.isUnit_iff.mp <| h x.natAbs hx)

theorem isCoprime_abs {m n : ℤ} : IsCoprime m n ↔ IsCoprime |m| |n| := by
  cases' abs_choice m with hm hm <;> cases' abs_choice n with hn hn <;> rw [hm, hn]
  · exact (IsCoprime.neg_right_iff m n).symm
  · exact (IsCoprime.neg_left_iff m n).symm
  · exact (IsCoprime.neg_neg_iff m n).symm

theorem isCoprime_iff_coprime_natAbs {m n : ℤ} : IsCoprime m n ↔ Nat.coprime m.natAbs n.natAbs := by
  rw [isCoprime_abs, abs_eq_natAbs, abs_eq_natAbs, Nat.isCoprime_iff_coprime]

-- The `Nat` version of this exists: `Nat.squarefree_mul`.
theorem squarefree_mul {m n : ℤ} (hmn : IsCoprime m n) :
    Squarefree (m * n) ↔ Squarefree m ∧ Squarefree n := by
  simp_rw [squarefree_iff_squarefree_natAbs, natAbs_mul]
  exact Nat.squarefree_mul (isCoprime_iff_coprime_natAbs.mp hmn)

theorem isCoprime_of_squarefree_mul {a b : ℤ} (h : Squarefree (a * b)) : IsCoprime a b := by
  by_contra hf
  obtain ⟨p, hp, ⟨a', ha⟩, ⟨b', hb⟩⟩ := not_isCoprime_iff_exists_prime_dvd.mp hf
  have hd : ↑(p * p) ∣ a * b := ⟨a' * b', by rw [ha, hb]; push_cast ; ring⟩
  exact hp.not_unit (ofNat_isUnit.mp <| h p hd)

-- The `Nat` version of this exists: `Nat.sq_mul_squarefree`.
theorem sq_mul_squarefree (n : ℤ) : ∃ a b : ℤ, b ^ 2 * a = n ∧ Squarefree a := by
  obtain ⟨a', b', h, hs⟩ := Nat.sq_mul_squarefree n.natAbs
  cases' natAbs_eq n with hn hn
  · exact ⟨a', b', by rw [hn]; exact_mod_cast h, squarefree_coe_nat.mpr hs⟩
  · exact ⟨-a', b', by rw [hn, ← h]; push_cast ; ring, (squarefree_coe_nat.mpr hs).neg⟩

end Int
