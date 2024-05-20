import LegendreQF.IsSquareMod

/-!
# Legendre's Theorem on ternary quadratic forms

We prove the following theorem originally due to Legendre.

Let $a$, $b$, $c$ be pairwise coprime and squarefree integers. Then the equation
$$ a x^2 + b y^2 + c z^2 = 0 $$
has a nontrivial integral solution $(x, y, z)$ if and only if
1. $a$, $b$ and $c$ do not all have the same sign and
2. $-bc$ is a square mod $a$, $-ca$ is a square mod $b$ and $-ab$ is a square mod $c$.

It is fairly easy to see that these conditions are necessary. The interesting
part of the statement is that they are sufficient.

We follow the proof given in [Ireland-Rosen].
-/


namespace Legendre

/-!
### Solubility predicate, assumptions on the coefficients and Legendre's conditions
-/


-- TODO: This can be done in principle for any ring in place of `ℤ`.
/-- We say that a triple of integers `a`, `b`, `c` is *soluble* if the equation
`a*x^2 + b*y^2 + c*z^2 = 0` has a nontrivial solution in integers. -/
def IsSoluble (a b c : ℤ) : Prop :=
  ∃ x y z, a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0 ∧ (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0)

/-- Solubility is preserved when the first two coefficients are swapped. -/
theorem IsSoluble.swap₁₂ {a b c : ℤ} (h : IsSoluble a b c) : IsSoluble b a c := by
  obtain ⟨x, y, z, h, hnt⟩ := h
  exact ⟨y, x, z, by rw [← h]; ring, by tauto⟩

/-- Solubility is preserved when the first and the last coefficient are swapped. -/
theorem IsSoluble.swap₁₃ {a b c : ℤ} (h : IsSoluble a b c) : IsSoluble c b a := by
  obtain ⟨x, y, z, h, hnt⟩ := h
  exact ⟨z, y, x, by rw [← h]; ring, by tauto⟩

/-- Solubility is preserved when the coefficients are rotated. -/
theorem IsSoluble.rotate {a b c : ℤ} (h : IsSoluble a b c) : IsSoluble b c a := by
  obtain ⟨x, y, z, h, hnt⟩ := h
  exact ⟨y, z, x, by rw [← h]; ring, by tauto⟩

/-- Solubility is preserved when the coefficients are multiplied by the same nonzero integer. -/
theorem IsSoluble.iff_scale {a b c d : ℤ} (hd : d ≠ 0) :
    IsSoluble a b c ↔ IsSoluble (d * a) (d * b) (d * c) := by
  refine' ⟨fun h => _, fun h => _⟩
  · obtain ⟨x, y, z, h, hnt⟩ := h
    refine' ⟨x, y, z, _, hnt⟩
    apply_fun (· * ·) d at h
    rw [MulZeroClass.mul_zero] at h
    rw [← h]
    ring
  · obtain ⟨x, y, z, h, hnt⟩ := h
    refine' ⟨x, y, z, _, hnt⟩
    have :
      d * a * x ^ 2 + d * b * y ^ 2 + d * c * z ^ 2 = d * (a * x ^ 2 + b * y ^ 2 + c * z ^ 2) := by
      ring
    rw [this, mul_eq_zero] at h
    exact h.resolve_left hd

/-- Solubility is preserved when the coefficients are negated. -/
theorem IsSoluble.neg {a b c : ℤ} (h : IsSoluble a b c) : IsSoluble (-a) (-b) (-c) := by
  obtain ⟨x, y, z, h, hnt⟩ := h
  refine' ⟨x, y, z, _, hnt⟩
  simp_rw [neg_mul, ← neg_add, h]

theorem IsSoluble.mul_iff_mul_mul {a b c d : ℤ} (hd : d ≠ 0) :
    IsSoluble (a * d) (b * d) c ↔ IsSoluble a b (c * d) := by
  refine' ⟨fun h => _, fun h => _⟩
  · obtain ⟨x, y, z, h, h₀⟩ := h
    refine' ⟨d * x, d * y, z, _, _⟩
    · apply_fun (· * ·) d at h
      rw [MulZeroClass.mul_zero] at h
      rw [← h]
      ring
    · rcases h₀ with (h₀ | h₀ | h₀)
      · exact Or.inl (mul_ne_zero hd h₀)
      · exact Or.inr (Or.inl <| mul_ne_zero hd h₀)
      · exact Or.inr (Or.inr h₀)
  · obtain ⟨x, y, z, h, h₀⟩ := h
    refine' ⟨x, y, d * z, _, _⟩
    · apply_fun (· * ·) d at h
      rw [MulZeroClass.mul_zero] at h
      rw [← h]
      ring
    · rcases h₀ with (h₀ | h₀ | h₀)
      · exact Or.inl h₀
      · exact Or.inr (Or.inl h₀)
      · exact Or.inr (Or.inr <| mul_ne_zero hd h₀)

theorem IsSoluble.iff_mul_sq {a b c d : ℤ} (hd : d ≠ 0) :
    IsSoluble a b (c * d ^ 2) ↔ IsSoluble a b c := by
  refine' ⟨fun h => _, fun h => _⟩
  · obtain ⟨x, y, z, h, h₀⟩ := h
    refine' ⟨x, y, d * z, by rw [← h]; ring, _⟩
    · rcases h₀ with (h₀ | h₀ | h₀)
      · exact Or.inl h₀
      · exact Or.inr (Or.inl h₀)
      · exact Or.inr (Or.inr <| mul_ne_zero hd h₀)
  · obtain ⟨x, y, z, h, h₀⟩ := h
    refine' ⟨d * x, d * y, z, _, _⟩
    · apply_fun (· * ·) (d ^ 2) at h
      rw [MulZeroClass.mul_zero] at h
      rw [← h]
      ring
    · rcases h₀ with (h₀ | h₀ | h₀)
      · exact Or.inl (mul_ne_zero hd h₀)
      · exact Or.inr (Or.inl <| mul_ne_zero hd h₀)
      · exact Or.inr (Or.inr h₀)

/-- If a triple is soluble, then there is a solution in coprime integers. -/
theorem IsSoluble.primitive {a b c : ℤ} (h : IsSoluble a b c) :
    ∃ x y z, a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0 ∧ x.gcd (y.gcd z) = 1 := by
  obtain ⟨x, y, z, h, hnt⟩ := h
  obtain ⟨g, x₁, y₁, z₁, hg, hgx, hgy, hgz, hg'⟩ := Int.make_primitive_3 x y z
  refine' ⟨x₁, y₁, z₁, _, hg'⟩
  rw [hgx, hgy, hgz] at h
  have hg₀ : 0 < g := by
    rwa [hg, Nat.cast_pos, Int.gcd_pos_iff, Nat.cast_ne_zero, ← zero_lt_iff, Int.gcd_pos_iff]
  apply_fun (· * ·) (g ^ 2) using mul_right_injective₀ (pow_ne_zero 2 hg₀.ne')
  dsimp only
  rw [MulZeroClass.mul_zero, ← h]
  ring

/-- This is the assumption on the coefficients in Legendre's Theorem:
they are coprime in pairs and squarefree. -/
def CoeffAss (a b c : ℤ) : Prop :=
  IsCoprime a b ∧ IsCoprime b c ∧ IsCoprime c a ∧ Squarefree a ∧ Squarefree b ∧ Squarefree c

/-- The assumptions are preserved when the first two coefficients are swapped. -/
theorem CoeffAss.swap₁₂ {a b c : ℤ} (h : CoeffAss a b c) : CoeffAss b a c := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  exact ⟨h₁.symm, h₃.symm, h₂.symm, h₅, h₄, h₆⟩

/-- The assumptions are preserved when the first and the last coefficient are swapped. -/
theorem CoeffAss.swap₁₃ {a b c : ℤ} (h : CoeffAss a b c) : CoeffAss c b a := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  exact ⟨h₂.symm, h₁.symm, h₃.symm, h₆, h₅, h₄⟩

/-- The assumptions are preserved when the coefficients are rotated. -/
theorem CoeffAss.rotate {a b c : ℤ} (h : CoeffAss a b c) : CoeffAss b c a := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  exact ⟨h₂, h₃, h₁, h₅, h₆, h₄⟩

theorem CoeffAss.neg_last {a b c : ℤ} (h : CoeffAss a b c) : CoeffAss a b (-c) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  exact ⟨h₁, h₂.neg_right, h₃.neg_left, h₄, h₅, h₆.neg⟩

theorem CoeffAss.neg_all {a b c : ℤ} (h : CoeffAss a b c) : CoeffAss (-a) (-b) (-c) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  exact ⟨h₁.neg_neg, h₂.neg_neg, h₃.neg_neg, h₄.neg, h₅.neg, h₆.neg⟩

theorem IsSoluble.primitive'_help₂ {a b c x y z : ℤ} (h : CoeffAss a b c)
    (hs : a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0) (hg : x.gcd (y.gcd z) = 1) : IsCoprime x y := by
  rw [← Int.gcd_eq_one_iff_coprime, Nat.eq_one_iff_not_exists_prime_dvd]
  intro p hp
  by_contra' hf
  obtain ⟨x₁, rfl⟩ : ↑p ∣ x := by
    rw [← Int.coe_nat_dvd] at hf
    exact hf.trans (Int.gcd_dvd_left _ _)
  obtain ⟨y₁, rfl⟩ : ↑p ∣ y := by
    rw [← Int.coe_nat_dvd] at hf
    exact hf.trans (Int.gcd_dvd_right _ _)
  rw [add_eq_zero_iff_neg_eq, mul_pow, mul_pow, ← mul_assoc, ← mul_assoc, mul_comm a, mul_comm b,
    mul_assoc, mul_assoc, ← mul_add, ← mul_neg, sq, mul_assoc] at hs
  have hpcz : (p : ℤ) ∣ c * z ^ 2 := ⟨_, hs.symm⟩
  have hpz : ¬↑p ∣ z := by
    by_contra' hpz
    obtain ⟨z₁, rfl⟩ := hpz
    rw [Int.gcd_mul_left, Int.natAbs_ofNat, Nat.cast_mul, Int.gcd_mul_left, Int.natAbs_ofNat] at hg
    exact hp.not_dvd_one ⟨_, hg.symm⟩
  cases' Int.Prime.dvd_mul' hp hpcz with hpc hpz₂
  · obtain ⟨c₁, rfl⟩ := hpc
    rw [mul_assoc] at hs
    replace hs := (mul_right_inj' (show (↑p : ℤ) ≠ 0 by exact_mod_cast hp.ne_zero)).mp hs
    have hpc₁z : (p : ℤ) ∣ c₁ * z ^ 2 := ⟨_, hs.symm⟩
    cases' Int.Prime.dvd_mul' hp hpc₁z with hpc₁ hpz₂'
    · obtain ⟨c₂, rfl⟩ := hpc₁
      replace h := h.2.2.2.2.2
      rw [← mul_assoc] at h
      replace h := h (↑p) (dvd_mul_right ((p : ℤ) * ↑p) c₂)
      exact (Prime.not_unit <| Nat.prime_iff_prime_int.mp hp) h
    · exact hpz (Int.Prime.dvd_pow' hp hpz₂')
  · exact hpz (Int.Prime.dvd_pow' hp hpz₂)

theorem IsSoluble.primitive'_help₁ {a b c x y z : ℤ} (h : CoeffAss a b c)
    (hs : a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0) (hg : x.gcd (y.gcd z) = 1) : IsCoprime a y := by
  rw [← Int.gcd_eq_one_iff_coprime, Nat.eq_one_iff_not_exists_prime_dvd]
  intro p hp
  by_contra' hf
  have hyz : IsCoprime y z :=
    by
    replace hs : b * y ^ 2 + c * z ^ 2 + a * x ^ 2 = 0 := by rw [← hs]; ring
    replace hg : y.gcd (z.gcd x) = 1 := by rwa [← Int.gcd_assoc, Int.gcd_comm]
    exact IsSoluble.primitive'_help₂ h.rotate hs hg
  obtain ⟨a₁, rfl⟩ : ↑p ∣ a := by
    rw [← Int.coe_nat_dvd] at hf
    exact hf.trans (Int.gcd_dvd_left _ _)
  obtain ⟨y₁, rfl⟩ : ↑p ∣ y := by
    rw [← Int.coe_nat_dvd] at hf
    exact hf.trans (Int.gcd_dvd_right _ _)
  rw [add_eq_zero_iff_neg_eq, mul_pow, ← mul_assoc, mul_comm b, sq (p : ℤ), mul_assoc, mul_assoc,
    mul_assoc, ← mul_add, ← mul_neg] at hs
  have hpcz : (p : ℤ) ∣ c * z ^ 2 := ⟨_, hs.symm⟩
  cases' Int.Prime.dvd_mul' hp hpcz with hpc hpz₂
  · obtain ⟨c₁, rfl⟩ := hpc
    exact Int.not_isCoprime_of_mul_prime hp _ _ h.2.2.1
  · obtain ⟨z₁, rfl⟩ := Int.Prime.dvd_pow' hp hpz₂
    exact Int.not_isCoprime_of_mul_prime hp _ _ hyz

theorem IsSoluble.primitive'_help {a b c x y z : ℤ} (h : CoeffAss a b c)
    (hs : a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0) (hg : x.gcd (y.gcd z) = 1) :
    IsCoprime (a * x) (b * y) := by
  refine' IsCoprime.mul_left _ _ <;> refine' IsCoprime.mul_right _ _
  · exact h.1
  · exact IsSoluble.primitive'_help₁ h hs hg
  · replace hs : b * y ^ 2 + a * x ^ 2 + c * z ^ 2 = 0 := by rw [← hs]; ring
    replace hg : y.gcd (x.gcd z) = 1 := by rwa [Int.gcd_comm x, ← Int.gcd_assoc, Int.gcd_comm _ x]
    exact (IsSoluble.primitive'_help₁ h.swap₁₂ hs hg).symm
  · exact IsSoluble.primitive'_help₂ h hs hg

/-- If a coefficient triple `(a,b,c)` is soluble and satisfies `CoeffAss`, then there is
a solution `(x,y,z)` such that `a*x`, `b*y` and `c*z` are coprime in pairs. -/
theorem IsSoluble.primitive' {a b c : ℤ} (h : IsSoluble a b c) (h' : CoeffAss a b c) :
    ∃ x y z,
      a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0 ∧
        IsCoprime (a * x) (b * y) ∧ IsCoprime (b * y) (c * z) ∧ IsCoprime (c * z) (a * x) := by
  obtain ⟨x, y, z, hs, hg⟩ := h.primitive
  refine' ⟨x, y, z, hs, IsSoluble.primitive'_help h' hs hg, _, _⟩
  · have hs' : b * y ^ 2 + c * z ^ 2 + a * x ^ 2 = 0 := by rw [← hs]; ring
    have hg' : y.gcd (z.gcd x) = 1 := by rwa [Int.gcd_comm, Int.gcd_assoc] at hg
    exact IsSoluble.primitive'_help h'.rotate hs' hg'
  · have hs' : c * z ^ 2 + a * x ^ 2 + b * y ^ 2 = 0 := by rw [← hs]; ring
    have hg' : z.gcd (x.gcd y) = 1 := by rwa [Int.gcd_comm, Int.gcd_assoc]
    exact IsSoluble.primitive'_help h'.rotate.rotate hs' hg'

/-- This is the first solubility conditions in Legendre's Theorem: the coefficients
do not all have the same sign. -/
def Condition₁ (a b c : ℤ) : Prop :=
  ¬(0 < a ∧ 0 < b ∧ 0 < c) ∧ ¬(a < 0 ∧ b < 0 ∧ c < 0)

theorem condition₁_iff {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    Condition₁ a b c ↔
      0 < a ∧ 0 < b ∧ c < 0 ∨
        0 < a ∧ b < 0 ∧ 0 < c ∨
          a < 0 ∧ 0 < b ∧ 0 < c ∨
            a < 0 ∧ b < 0 ∧ 0 < c ∨ a < 0 ∧ 0 < b ∧ c < 0 ∨ 0 < a ∧ b < 0 ∧ c < 0 := by
  dsimp only [Condition₁]
  cases' ha.lt_or_lt with ha₁ ha₁ <;>
        simp only [asymm ha₁, ha₁, false_and_iff, not_false_iff, true_and_iff, not_and, not_lt,
          false_and_iff, not_false_iff, or_false_iff, false_or_iff, and_true_iff] <;>
      cases' hb.lt_or_lt with hb₁ hb₁ <;>
    simp only [asymm hb₁, hb₁, IsEmpty.forall_iff, forall_true_left, false_and_iff, true_and_iff,
      or_false_iff, false_or_iff, lt_or_lt_iff_ne, Ne.def, true_iff_iff, le_iff_eq_or_lt, hc.symm,
      hc, not_false_iff, or_iff_right_iff_imp]

/-- This is the second solubility condition in Legendre's theorem: the negative product
of each pair of coefficients is a square modulo the third. -/
def Condition₂ (a b c : ℤ) : Prop :=
  IsSquareMod (-b * c) a ∧ IsSquareMod (-a * c) b ∧ IsSquareMod (-a * b) c

theorem Condition₂.rotate {a b c : ℤ} (h : Condition₂ a b c) : Condition₂ b c a := by
  have H : ∀ x y : ℤ, -x * y = -y * x := fun x y => by ring
  obtain ⟨ha, hb, hc⟩ := h
  rw [H] at hb hc
  exact ⟨hb, hc, ha⟩

theorem Condition₂.neg {a b c : ℤ} (h : Condition₂ a b c) : Condition₂ (-a) (-b) (-c) := by
  have H : ∀ x y : ℤ, - -x * -y = -x * y := fun x y => by ring
  obtain ⟨ha, hb, hc⟩ := h
  rw [← IsSquareMod.iff_neg, ← H] at ha hb hc
  exact ⟨ha, hb, hc⟩

/-!
### The conditions are necessary
-/


/-- The first condition in Legendre's Theorem is necessary. -/
theorem necessary₁ {a b c : ℤ} (h : IsSoluble a b c) : ¬(0 < a ∧ 0 < b ∧ 0 < c) := by
  obtain ⟨x, y, z, h, hnt⟩ := h
  contrapose! hnt
  have hx := mul_nonneg hnt.1.le (sq_nonneg x)
  have hy := mul_nonneg hnt.2.1.le (sq_nonneg y)
  have hz := mul_nonneg hnt.2.2.le (sq_nonneg z)
  replace hx : a * x ^ 2 = 0 := by linarith
  replace hy : b * y ^ 2 = 0 := by linarith
  replace hz : c * z ^ 2 = 0 := by linarith
  rw [mul_eq_zero, sq_eq_zero_iff] at hx hy hz
  exact ⟨hx.resolve_left hnt.1.ne', hy.resolve_left hnt.2.1.ne', hz.resolve_left hnt.2.2.ne'⟩

/-- The second condition in Legendre's Theorem is necessary. -/
theorem necessary₂ {a b c : ℤ} (h : IsSoluble a b c) (h' : CoeffAss a b c) :
    IsSquareMod (-b * c) a := by
  obtain ⟨x, y, z, h, haxby, hbycz, hczax⟩ := IsSoluble.primitive' h h'
  rw [add_eq_zero_iff_eq_neg] at h
  apply_fun (· * ·) b at h
  rw [mul_neg, ← mul_assoc, ← neg_mul, mul_add, ← mul_assoc, ← mul_assoc, mul_comm _ a, mul_assoc, ←
    sq, ← mul_pow, ← eq_sub_iff_add_eq, ← neg_mul] at h
  have H : IsSquareMod (-b * c * z ^ 2) a := ⟨b * y, _, h.symm⟩
  have hcz : IsCoprime a z := IsCoprime.of_mul_left_left (IsCoprime.of_mul_right_right hczax.symm)
  exact H.of_mul_sq_of_coprime_left hcz

/-- The conditions in Legendre's Theorem are necessary. -/
theorem necessary {a b c : ℤ} (h : IsSoluble a b c) (h' : CoeffAss a b c) :
    Condition₁ a b c ∧ Condition₂ a b c := by
  refine'
    ⟨⟨necessary₁ h, _⟩,
      ⟨necessary₂ h h', necessary₂ h.swap₁₂ h'.swap₁₂, necessary₂ h.rotate.rotate h'.rotate.rotate⟩⟩
  have := necessary₁ h.neg
  simpa [neg_pos] using this

/-!
### The conditions are sufficient

We show the following eqivalent statment:

If `a` and `b` are positive squarefree integers such that `a` is a square mod `b`,
`b` is a square mod `a` and `-a*b/d^2` is a square mod `d = gcd a b`, then the equation
`a*x^2 + b*y^2 = z^2` has a nontrivial solution in integers `x`, `y`, `z`.

We then show that this implies the sufficiency direction in Legendre's Theorem.
-/


/-- A special case: The equation `b*x^2 + b*y^2 = z^2` has a nontrivial solution
if `b` is positive and `-1` is a square modulo `b`. -/
theorem isSoluble_equal {b : ℤ} (hb : 0 < b) (h : IsSquareMod (-1) b) : IsSoluble b b (-1) := by
  obtain ⟨r, s, hrs⟩ := h.sum_of_squares_of_isSquareMod_neg_one hb.le
  exact ⟨r, s, r ^ 2 + s ^ 2, by rw [hrs]; ring, Or.inr <| Or.inr <| by rw [← hrs]; exact hb.ne'⟩

/-- This lemma is used to reduce the statement for `a` and `b` to the statement for `A` and `b`
with some `0 < A < a`. -/
theorem descent {a b : ℤ} (hb : 0 < b) (hba : b < a) (h : IsSquareMod b a) :
    ∃ A c m : ℤ, c ^ 2 - b = a * (m ^ 2 * A) ∧ Squarefree A ∧ 0 < A ∧ A < a := by
  obtain ⟨c, t, h₁, h₂, h₃⟩ := h.exists_le_half (hb.trans hba)
  have ht₀ : t ≤ 0 := by nlinarith
  rcases ht₀.eq_or_lt with (rfl | htn)
  · change 1 ≤ b at hb
    exact ⟨1, c, 0, by linear_combination -h₁, squarefree_one, zero_lt_one, hb.trans_lt hba⟩
  obtain ⟨A, m, ht, hA⟩ := Int.sq_mul_squarefree (-t)
  have hA₀ : 0 < A := pos_of_mul_pos_right (by rwa [ht, neg_pos]) (sq_nonneg m)
  refine' ⟨A, c, m, by linear_combination -h₁ - a * ht, hA, hA₀, _⟩
  replace h₃ : 2 * c ≤ a :=
    ((mul_le_mul_left zero_lt_two).mpr h₃).trans (Int.mul_ediv_le zero_lt_two a)
  have H : a * (4 * m ^ 2 * A) < a * a := by
    calc
      a * (4 * m ^ 2 * A) = (2 * c) ^ 2 - 4 * b := by linear_combination 4 * h₁ + 4 * a * ht
      _ < (2 * c) ^ 2 := (Int.sub_lt_self _ (mul_pos zero_lt_four hb))
      _ ≤ a ^ 2 := (sq_le_sq' (by linarith [hb, hba, h₂]) h₃)
      _ = a * a := sq a
  have hm₀ : m ≠ 0 := by
    rintro rfl
    rw [zero_pow zero_lt_two, MulZeroClass.zero_mul, eq_comm, neg_eq_zero] at ht
    exact htn.ne ht
  calc
    A = 1 * A := (one_mul A).symm
    _ ≤ 4 * m ^ 2 * A := (mul_le_mul_of_nonneg_right (by change 0 < 4 * m ^ 2; positivity) hA₀.le)
    _ < a := lt_of_mul_lt_mul_left H (by linarith)

/-- This shows that the first condition, `is_square_mod a b` is preserved when we replace `a`
by `A` (as obtained from `legendre.descent`). -/
theorem condition_i {A a b c m : ℤ} (sa : Squarefree a) (sb : Squarefree b) (h₁ : IsSquareMod a b)
    (h₃ : IsSquareMod (-a * b / (a.gcd b : ℤ) ^ 2) (a.gcd b : ℤ))
    (h' : c ^ 2 - b = a * (m ^ 2 * A)) :
    IsSquareMod A b := by
  obtain ⟨g, a₁, b₁, c₁, hg, rfl, rfl, rfl, h⟩ := Int.make_primitive_3 a b c
  have hg₀ : g ≠ 0 := left_ne_zero_of_mul sa.ne_zero
  have hag := Int.isCoprime_of_squarefree_mul sa
  have hbg := Int.isCoprime_of_squarefree_mul sb
  replace h' : g * (c₁ ^ 2 * g - b₁) = g * (a₁ * (m ^ 2 * A)) := by linear_combination h'
  replace h' := mul_left_cancel₀ hg₀ h'
  have hg₁ : IsCoprime a₁ b₁ := by
    by_contra hf
    obtain ⟨p, hp, ⟨a₁, rfl⟩, ⟨b₁, rfl⟩⟩ := Int.not_isCoprime_iff_exists_prime_dvd.mp hf
    have H : (p : ℤ) ∣ c₁ ^ 2 * g := ⟨b₁ + a₁ * (m ^ 2 * A), by linear_combination h'⟩
    obtain ⟨c₁, rfl⟩ := Int.Prime.dvd_pow' hp (hbg.of_mul_right_left.symm.dvd_of_dvd_mul_right H)
    simp only [Int.gcd_mul_left, Nat.cast_mul, Int.natAbs_ofNat] at h
    exact hp.not_dvd_one ⟨_, h.symm⟩
  rw [Int.gcd_mul_left, Int.gcd_eq_one_iff_coprime.mpr hg₁, mul_one, Int.natAbs_sq, ←
    IsSquareMod.iff_natAbs, (by ring : -(g * a₁) * (g * b₁) = -a₁ * b₁ * g ^ 2),
    Int.mul_ediv_cancel _ (pow_ne_zero 2 hg₀)] at h₃
  refine' IsSquareMod.mul_of_coprime _ _ hbg
  · have H := IsCoprime.mul_add_right_right hbg.neg_right (c₁ ^ 2)
    rw [← sub_eq_add_neg, h', sq, ← mul_assoc, mul_comm a₁, mul_assoc, mul_assoc] at H
    apply_fun (· * ·) a₁ at h'
    rw [mul_sub, sub_eq_add_neg, ← eq_sub_iff_add_eq, ← mul_assoc, mul_comm _ g, ← neg_mul,
      (by ring : a₁ * (a₁ * (m ^ 2 * A)) = A * (a₁ * m) ^ 2)] at h'
    exact
      (h₃.of_dvd_sub ⟨_, h'.symm⟩).of_mul_sq_of_coprime_left (hag.mul_right H.of_mul_right_left)
  · have ha := IsCoprime.mul_left hbg hg₁
    have hsm : IsSquareMod (g * a₁ * (m ^ 2 * A)) b₁ := ⟨c₁ * g, -g, by linear_combination -g * h'⟩
    have hm : IsCoprime b₁ m := by
      by_contra hf
      obtain ⟨p, hp, ⟨b₂, rfl⟩, ⟨m', rfl⟩⟩ := Int.not_isCoprime_iff_exists_prime_dvd.mp hf
      rw [sub_eq_iff_eq_add] at h'
      have H : (p : ℤ) ∣ c₁ ^ 2 * g := ⟨a₁ * p * m' ^ 2 * A + b₂, by rw [h']; ring⟩
      obtain ⟨c₂, rfl⟩ := Int.Prime.dvd_pow' hp (hbg.symm.of_mul_left_left.dvd_of_dvd_mul_right H)
      obtain ⟨b₃, rfl⟩ : ↑p ∣ b₂ :=
        by
        refine' ⟨c₂ ^ 2 * g - a₁ * m' ^ 2 * A, _⟩
        have : Function.Injective ((· * ·) (p : ℤ)) :=
          mul_right_injective₀ (Nat.cast_ne_zero.mpr hp.ne_zero)
        apply_fun (· * ·) (p : ℤ) using this
        linear_combination -h'
      exact hp.not_unit (Int.ofNat_isUnit.mp <| sb (p : ℤ) ⟨b₃ * g, by ring⟩)
    exact (hsm.of_mul h₁.of_mul_right ha).of_mul_sq_of_coprime_right hm

/-- This shows that the third condition, `IsSquareMod (-a*b/(a.gcd b)^2) (a.gcd b)`
is preserved when we replace `a` by `A` (as obtained from `legendre.descent`). -/
theorem condition_iii {A a b c m : ℤ} (sb : Squarefree b) (h₁ : IsSquareMod a b)
    (h' : c ^ 2 - b = a * (m ^ 2 * A)) :
    IsSquareMod (-A * b / (A.gcd b : ℤ) ^ 2) (A.gcd b : ℤ) := by
  obtain ⟨g, A₁, b₁, c₁, hg, rfl, rfl, rfl, h⟩ := Int.make_primitive_3 A b c
  have hg₀ : g ≠ 0 := left_ne_zero_of_mul sb.ne_zero
  have hbg := Int.isCoprime_of_squarefree_mul sb
  replace h' : g * (c₁ ^ 2 * g - b₁) = g * (a * (m ^ 2 * A₁)) := by linear_combination h'
  replace h' := mul_left_cancel₀ hg₀ h'
  have hg₁ : IsCoprime A₁ b₁ := by
    -- maybe prove a lemma; see similar statement above
    by_contra hf
    obtain ⟨p, hp, ⟨A₂, rfl⟩, ⟨b₂, rfl⟩⟩ := Int.not_isCoprime_iff_exists_prime_dvd.mp hf
    have H : (p : ℤ) ∣ c₁ ^ 2 * g := ⟨b₂ + a * (m ^ 2 * A₂), by linear_combination h'⟩
    obtain ⟨c₂, rfl⟩ := Int.Prime.dvd_pow' hp (hbg.of_mul_right_left.symm.dvd_of_dvd_mul_right H)
    simp only [Int.gcd_mul_left, Nat.cast_mul, Int.natAbs_ofNat] at h
    exact hp.not_dvd_one ⟨_, h.symm⟩
  rw [Int.gcd_mul_left, Int.gcd_eq_one_iff_coprime.mpr hg₁, mul_one, Int.natAbs_sq, ←
    IsSquareMod.iff_natAbs, (by ring : -(g * A₁) * (g * b₁) = -A₁ * b₁ * g ^ 2),
    Int.mul_ediv_cancel _ (pow_ne_zero 2 hg₀)]
  obtain ⟨u, v, huv⟩ := h₁.of_mul_left
  exact
    ⟨u * m * A₁, A₁ * (v * m ^ 2 * A₁ - c₁ ^ 2), by
      linear_combination A₁ * h' + A₁ ^ 2 * m ^ 2 * huv⟩

/-- If we have a solution for `A` and `b` (with `A` obtained from `legendre.descent`),
then there is also a solution for `a` and `b`. -/
theorem isSoluble_transfer {A a b c m : ℤ} (hm : m ≠ 0) (hA : A ≠ 0) (ha : a ≠ 0)
    (h : IsSoluble A b (-1)) (h' : c ^ 2 - b = a * (m ^ 2 * A)) : IsSoluble a b (-1) := by
  obtain ⟨x, y, z, h, hnt⟩ := h
  refine'
    ⟨m * A * x, c * y + z, b * y + c * z, by
      linear_combination a * m ^ 2 * A * h + (b * y ^ 2 - z ^ 2) * h', _⟩
  by_contra' hf
  obtain ⟨h₁, h₂, h₃⟩ := hf
  have hy : (c ^ 2 - b) * y = 0 := by linear_combination c * h₂ - h₃
  have hz : (c ^ 2 - b) * z = 0 := by linear_combination -b * h₂ + c * h₃
  have hcb : c ^ 2 - b ≠ 0 := by
    rw [h']
    exact mul_ne_zero ha (mul_ne_zero (pow_ne_zero 2 hm) hA)
  rcases hnt with (hx' | hy' | hz')
  · exact hx' (eq_zero_of_ne_zero_of_mul_left_eq_zero (mul_ne_zero hm hA) h₁)
  · exact hy' (eq_zero_of_ne_zero_of_mul_left_eq_zero hcb hy)
  · exact hz' (eq_zero_of_ne_zero_of_mul_left_eq_zero hcb hz)

/-- This shows the variant of Legendre's Theorem under the additional assumption that `b < a`. -/
theorem isSoluble_neg_one_of_lt {a b : ℤ} (sa : Squarefree a) (sb : Squarefree b) (hb : 0 < b)
    (hba : b < a) (h₁ : IsSquareMod a b) (h₂ : IsSquareMod b a)
    (h₃ : IsSquareMod (-a * b / (a.gcd b : ℤ) ^ 2) (a.gcd b : ℤ)) : IsSoluble a b (-1) := by
  lift b to ℕ using hb.le
  lift a to ℕ using (hb.trans hba).le
  induction' a using Nat.strong_induction_on with a ih generalizing b
  obtain ⟨A, c, m, h', sf, hA, te⟩ := descent hb hba h₂
  rcases eq_or_ne m 0 with (rfl | hm)
  · exact ⟨0, 1, c, by linear_combination -h', Or.inr (Or.inl one_ne_zero)⟩
  have b1 := condition_i sa sb h₁ h₃ h'
  have b2 : IsSquareMod (b : ℤ) A := ⟨c, -a * m ^ 2, by linear_combination -h'⟩
  have b3 := condition_iii sb h₁ h'
  lift A to ℕ using hA.le
  refine' isSoluble_transfer hm sf.ne_zero sa.ne_zero _ h'
  rcases lt_trichotomy A b with (hAb | rfl | hAb)
  · rw [neg_mul, mul_comm, ← neg_mul, Int.gcd_comm] at b3
    exact (ih b (Nat.cast_lt.mp hba) _ sf hA sb (Nat.cast_lt.mpr hAb) b2 b1 b3).swap₁₂
  · rw [neg_mul, Int.gcd_self, Int.natAbs_ofNat, ← sq, Int.neg_ediv_of_dvd (Int.dvd_refl _),
        Int.ediv_self (sq_pos_of_ne_zero _ hb.ne').ne'] at b3
    exact isSoluble_equal hb b3
  · exact ih A (Nat.cast_lt.mp te) _ sb hb sf (Nat.cast_lt.mpr hAb) b1 b2 b3

/-- This is the (interesting direction of) the variant of Legendre's Theorem:
if `a` and `b` are positive and squarefree, `a` is a square modulo `b`, `b` is a square
modulo `a`, and `-a*b/(a.gcd b)^2` is a square modulo `a.gcd b`, then the equation
`a*x^2 + b*y^2 = z^2` has a nontrivial solution in integers. -/
theorem isSoluble_neg_one {a b : ℤ} (ha₀ : 0 < a) (hb₀ : 0 < b) (ha : Squarefree a)
    (hb : Squarefree b) (hab : IsSquareMod a b) (hba : IsSquareMod b a)
    (hd : IsSquareMod (-a * b / (a.gcd b : ℤ) ^ 2) (a.gcd b : ℤ)) : IsSoluble a b (-1) := by
  rcases lt_trichotomy a b with (hab' | rfl | hab')
  · rw [neg_mul, mul_comm, ← neg_mul, Int.gcd_comm] at hd
    exact (isSoluble_neg_one_of_lt hb ha ha₀ hab' hba hab hd).swap₁₂
  · rw [neg_mul, Int.gcd_self, ← sq, Int.natAbs_sq, Int.neg_ediv_of_dvd ⟨1, (mul_one _).symm⟩,
      Int.ediv_self (sq_pos_of_ne_zero _ hb₀.ne').ne', ← Int.eq_natAbs_of_zero_le ha₀.le] at hd
    exact isSoluble_equal ha₀ hd
  · exact isSoluble_neg_one_of_lt ha hb hb₀ hab' hab hba hd

/-- This shows the sufficiency of the conditions in Legendre's Theorem when the first two
coefficients are positive and the last is negative. -/
theorem sufficient' {a b c : ℤ} (ha₁ : 0 < a) (hb₁ : 0 < b) (hc₁ : 0 < c) (h₂ : Condition₂ a b (-c))
    (h' : CoeffAss a b c) : IsSoluble a b (-c) := by
  obtain ⟨ha₂, hb₂, hc₂⟩ := h₂
  obtain ⟨hab, hbc, hca, ha, hb, hc⟩ := h'
  rw [neg_mul_neg] at ha₂ hb₂
  rw [IsSquareMod.iff_neg, neg_mul] at hc₂
  rw [(by ring : -c = -1 * c), ← IsSoluble.mul_iff_mul_mul hc₁.ne']
  refine'
    isSoluble_neg_one (mul_pos ha₁ hc₁) (mul_pos hb₁ hc₁)
      ((Int.squarefree_mul hca.symm).mpr ⟨ha, hc⟩) ((Int.squarefree_mul hbc).mpr ⟨hb, hc⟩)
      (hb₂.mul_of_coprime (isSquareMod_mul_self a c) hbc)
      (ha₂.mul_of_coprime (isSquareMod_mul_self b c) hca.symm) _
  have hg : ((a * c).gcd (b * c) : ℤ) = c := by
    rw [Int.gcd_mul_right, Int.gcd_eq_one_iff_coprime.mpr hab, one_mul, Int.natAbs_of_nonneg hc₁.le]
  rwa [hg, neg_mul, (by ring : a * c * (b * c) = a * b * c ^ 2), ← neg_mul,
    Int.mul_ediv_cancel _ (pow_ne_zero 2 hc₁.ne')]

/-- This shows that the conditions in Legendre's Theorem are sufficient. -/
theorem sufficient {a b c : ℤ} (h₁ : Condition₁ a b c) (h₂ : Condition₂ a b c)
    (h' : CoeffAss a b c) : IsSoluble a b c := by
  have h'' := h' ; obtain ⟨hab, hbc, hca, ha, hb, hc⟩ := h''
  clear hab hbc hca
  rcases(condition₁_iff ha.ne_zero hb.ne_zero hc.ne_zero).mp h₁ with (H | H | H | H | H | H)
  · rw [← neg_neg c] at h₂ H ⊢
    exact sufficient' H.1 H.2.1 (neg_lt_zero.mp H.2.2) h₂ h'.neg_last
  · rw [← neg_neg b] at h₂ H ⊢
    exact
      IsSoluble.rotate
        (sufficient' H.2.2 H.1 (neg_lt_zero.mp H.2.1) h₂.rotate.rotate h'.rotate.rotate.neg_last)
  · rw [← neg_neg a] at h₂ H ⊢
    exact
      IsSoluble.rotate
        (IsSoluble.rotate <|
          sufficient' H.2.1 H.2.2 (neg_lt_zero.mp H.1) h₂.rotate h'.rotate.neg_last)
  · rw [← neg_neg a, ← neg_neg b] at H ⊢
    rw [← neg_neg c]
    simp_rw [neg_lt_zero] at H
    refine' IsSoluble.neg (sufficient' H.1 H.2.1 H.2.2 h₂.neg _)
    rw [← neg_neg c]
    exact h'.neg_all.neg_last
  · rw [← neg_neg a, ← neg_neg c] at H ⊢
    rw [← neg_neg b]
    simp_rw [neg_lt_zero] at H
    refine' IsSoluble.neg (IsSoluble.rotate <| sufficient' H.2.2 H.1 H.2.1 h₂.rotate.rotate.neg _)
    rw [← neg_neg b]
    exact h'.rotate.rotate.neg_all.neg_last
  · rw [← neg_neg b, ← neg_neg c] at H ⊢
    rw [← neg_neg a]
    simp_rw [neg_lt_zero] at H
    refine'
      IsSoluble.neg
        (IsSoluble.rotate <| IsSoluble.rotate <| sufficient' H.2.1 H.2.2 H.1 h₂.rotate.neg _)
    rw [← neg_neg a]
    exact h'.rotate.neg_all.neg_last

/-- The main result: *Legendre's Theorem* on ternary quadratic forms. Let `a`, `b`, `c`
be pairwise coprime and squarefree integers. Then the equation `a*x^2 + b*y^2 + c*z^2 = 0`
has a nontrivial solution in integers if and only if not all of `a`, `b`, `c` have the
same sign and `-a*b` is a square modulo `c`, `-b*c` is a square modulo `a` and
`-a*c` is a square modulo `b`.
-/
theorem isSoluble_iff {a b c : ℤ} (h : CoeffAss a b c) :
    IsSoluble a b c ↔ Condition₁ a b c ∧ Condition₂ a b c :=
  ⟨fun H => necessary H h, fun H => sufficient H.1 H.2 h⟩

end Legendre

