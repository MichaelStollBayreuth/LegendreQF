import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Squarefree

/-!
### Useful lemmas
-/

-- Mathlib.Algebra.Squarefree
theorem Squarefree.neg {R} [Monoid R] [HasDistribNeg R] {r : R} (h : Squarefree r) :
    Squarefree (-r) := fun x hx ↦ h x (dvd_neg.mp hx)

namespace Int

-- The `Nat` version of this exists: `Nat.mul_div_le`.
-- Where should this go? Related lemmas are in Std.Data.Int.DivMod
-- Maybe Mathlib.Data.Int.Div?
theorem mul_ediv_le {m : ℤ} (h : 0 < m) (n : ℤ) : m * (n / m) ≤ n := by
  nth_rw 2 [← ediv_add_emod n m]
  simp only [emod_nonneg _ h.ne', le_add_iff_nonneg_right]

-- compare `Nat.exists_coprime` and `Nat.exists_coprime'`
/-- A pair of integers `a` and `b` can be made coprime by dividing them by their gcd. -/
theorem exists_gcd_eq_one (a b : ℤ) :
    ∃ g a₁ b₁ : ℤ, g = a.gcd b ∧ a = g * a₁ ∧ b = g * b₁ ∧ a₁.gcd b₁ = 1 := by
  by_cases h : a = 0 ∧ b = 0
  · refine ⟨0, 1, 1, ?_⟩
    simp only [h.1, h.2, gcd_self, natAbs_zero, Nat.cast_zero, mul_one, isUnit_one,
      natAbs_of_isUnit, and_self]
  · rw [not_and_or, ← Ne, ← Ne] at h
    have hg := gcd_pos_iff.mpr h
    have hg' : (gcd a b : ℤ) ≠ 0 := natCast_ne_zero_iff_pos.mpr hg
    refine ⟨a.gcd b, a / a.gcd b, b / a.gcd b, rfl, ?_, ?_, ?_⟩
    · rw [← Int.mul_ediv_assoc _ gcd_dvd_left]
      exact (Int.mul_ediv_cancel_left _ hg').symm
    · rw [← Int.mul_ediv_assoc _ gcd_dvd_right]
      exact (Int.mul_ediv_cancel_left _ hg').symm
    · exact gcd_div_gcd_div_gcd hg

-- #find_home! Int.exists_gcd_eq_one -- [Mathlib.Algebra.GCDMonoid.Nat] perhaps?

/-- A triple of integers `a`, `b`, `c` can be made coprime by dividing them by their gcd. -/
theorem exists_gcd_gcd_eq_one (a b c : ℤ) :
    ∃ g a₁ b₁ c₁ : ℤ,
      g = a.gcd (b.gcd c) ∧ a = g * a₁ ∧ b = g * b₁ ∧ c = g * c₁ ∧ a₁.gcd (b₁.gcd c₁) = 1 := by
  obtain ⟨g₁, b₂, c₂, hg₁, hgb, hgc, hg₁'⟩ := exists_gcd_eq_one b c
  obtain ⟨g, a₁, w, hg, hga, hgw, hg'⟩ := exists_gcd_eq_one a g₁
  rcases eq_or_ne g 0 with hg₀ | hg₀
  · simp only [hg₀, zero_mul] at hga hgw
    simp only [hgw, zero_mul] at hgb hgc
    rw [← hg₁, ← hg, hga, hgb, hgc, hg₀]
    refine ⟨0, 1, 1, 1, rfl, (zero_mul _).symm, (zero_mul _).symm, (zero_mul _).symm, ?_⟩
    simp only [gcd_self, isUnit_one, natAbs_of_isUnit, Nat.cast_one]
  · have hw₁ : 0 ≤ w := by
      have hg₁₀ : 0 ≤ g₁ := by rw [hg₁]; exact Nat.cast_nonneg _
      replace hg₀ : 0 < g :=
        (eq_or_lt_of_le <| by rw [hg]; exact Nat.cast_nonneg _).resolve_left hg₀.symm
      exact nonneg_of_mul_nonneg_right (hgw ▸ hg₁₀) hg₀
    exact ⟨g, a₁, w * b₂, w * c₂, by rwa [hg₁] at hg, hga, by rw [hgb, hgw, mul_assoc],
      by rw [hgc, hgw, mul_assoc], by simpa only [gcd_mul_left, hg₁', mul_one] using hg'⟩

-- The `Nat` and `gcd_monoid` versions of this exist: `Nat.dvd_gcd_iff`, `dvd_gcd_iff`.
-- Mathlib.RingTheory.Int.Basic
theorem dvd_gcd_iff {k : ℕ} {m n : ℤ} : k ∣ m.gcd n ↔ ↑k ∣ m ∧ ↑k ∣ n := by
  rw [gcd_eq_natAbs, natCast_dvd, natCast_dvd]
  exact Nat.dvd_gcd_iff

-- where should this go? #find_home does not help, since it uses `dvd_gcd_iff`
/-- Two integers are not coprime if and only if there is a prime number that divides both. -/
theorem not_isCoprime_iff_exists_prime_dvd {a b : ℤ} :
    ¬IsCoprime a b ↔ ∃ p : ℕ, p.Prime ∧ ↑p ∣ a ∧ ↑p ∣ b := by
  rw [isCoprime_iff_gcd_eq_one, Nat.eq_one_iff_not_exists_prime_dvd]
  push_neg
  simp_rw [dvd_gcd_iff]

/-- Two multiples of the same prime are not coprime. -/
theorem not_isCoprime_of_mul_prime {p : ℕ} (hp : p.Prime) (a b : ℤ) :
    ¬IsCoprime (↑p * a) (↑p * b) :=
  not_isCoprime_iff_exists_prime_dvd.mpr ⟨p, hp, dvd_mul_right .., dvd_mul_right ..⟩

-- Mathlib.Algebra.Squarefree
theorem squarefree_iff_squarefree_natAbs {n : ℤ} : Squarefree n ↔ Squarefree n.natAbs := by
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ ?_⟩
  · exact ofNat_isUnit.mp <| h x <| dvd_natAbs.mp <| ofNat_dvd_right.mpr hx
  · rw [← natAbs_dvd_natAbs, natAbs_mul] at hx
    exact isUnit_iff_natAbs_eq.mpr <| Nat.isUnit_iff.mp <| h x.natAbs hx

-- Mathlib.RingTheory.Coprime.Basic
theorem isCoprime_abs {m n : ℤ} : IsCoprime m n ↔ IsCoprime |m| |n| := by
  rcases abs_choice m with hm | hm <;> rcases abs_choice n with hn | hn <;> rw [hm, hn]
  · exact (IsCoprime.neg_right_iff m n).symm
  · exact (IsCoprime.neg_left_iff m n).symm
  · exact (IsCoprime.neg_neg_iff m n).symm

theorem isCoprime_iff_coprime_natAbs {m n : ℤ} :
    IsCoprime m n ↔ Nat.Coprime m.natAbs n.natAbs := by
  rw [isCoprime_abs, abs_eq_natAbs, abs_eq_natAbs, Nat.isCoprime_iff_coprime]

-- The `Nat` version of this exists: `Nat.squarefree_mul`.
theorem squarefree_mul {m n : ℤ} (hmn : IsCoprime m n) :
    Squarefree (m * n) ↔ Squarefree m ∧ Squarefree n := by
  simp_rw [squarefree_iff_squarefree_natAbs, natAbs_mul]
  exact Nat.squarefree_mul (isCoprime_iff_coprime_natAbs.mp hmn)

/-- If the product of two integers is squarefree, then the integers are coprime. -/
theorem isCoprime_of_squarefree_mul {a b : ℤ} (h : Squarefree (a * b)) : IsCoprime a b := by
  by_contra hf
  obtain ⟨p, hp, ⟨a', rfl⟩, ⟨b', rfl⟩⟩ := not_isCoprime_iff_exists_prime_dvd.mp hf
  have hd : ↑(p * p) ∣ p * a' * (p * b') := ⟨a' * b', by push_cast; ring⟩
  exact hp.not_isUnit (ofNat_isUnit.mp <| h p hd)

/-- A product of two integers is squarefree if and only if they are coprime and both squarefree. -/
lemma squarefree_mul_iff {a b : ℤ} :
    Squarefree (a * b) ↔ IsCoprime a b ∧ Squarefree a ∧ Squarefree b := by
  refine ⟨fun H ↦ ?_, fun ⟨hab, ha, hb⟩ ↦ (squarefree_mul hab).mpr ⟨ha, hb⟩⟩
  have := isCoprime_of_squarefree_mul H
  exact ⟨this, (squarefree_mul this).mp H⟩

-- The `Nat` version of this exists: `Nat.sq_mul_squarefree`.
/-- Any integer can be written as the product of a square and a squarefree integer. -/
theorem sq_mul_squarefree (n : ℤ) : ∃ a b : ℤ, b ^ 2 * a = n ∧ Squarefree a := by
  obtain ⟨a', b', h, hs⟩ := Nat.sq_mul_squarefree n.natAbs
  rcases natAbs_eq n with hn | hn
  · exact ⟨a', b', by rw [hn]; exact_mod_cast h, squarefree_natCast.mpr hs⟩
  · exact ⟨-a', b', by rw [hn, ← h]; push_cast; ring, (squarefree_natCast.mpr hs).neg⟩

end Int
