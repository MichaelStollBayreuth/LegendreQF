import LegendreQF.Auxiliary
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

This is based on code written in the context of the Bachelor's thesis of Anne Zahn.
-/


namespace Legendre

/-!
### Solubility predicate
-/

section General

variable {R : Type*} [CommRing R]

/-- We say that a triple of ring elements `a`, `b`, `c` is *soluble* if the equation
`a * x^2 + b * y^2 + c * z^2 = 0` has a nontrivial solution in the ring. -/
def IsSoluble (a b c : R) : Prop :=
  ∃ x y z, a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0 ∧ (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0)

namespace IsSoluble

/-- Solubility is preserved when the first two coefficients are swapped. -/
theorem swap₁₂ {a b c : R} (h : IsSoluble a b c) : IsSoluble b a c := by
  obtain ⟨x, y, z, h, hnt⟩ := h
  exact ⟨y, x, z, by rw [← h]; ring, by tauto⟩

/-- Solubility is preserved when the first and the last coefficient are swapped. -/
theorem swap₁₃ {a b c : R} (h : IsSoluble a b c) : IsSoluble c b a := by
  obtain ⟨x, y, z, h, hnt⟩ := h
  exact ⟨z, y, x, by rw [← h]; ring, by tauto⟩

/-- Solubility is preserved when the coefficients are rotated. -/
theorem rotate {a b c : R} (h : IsSoluble a b c) : IsSoluble b c a := by
  obtain ⟨x, y, z, h, hnt⟩ := h
  exact ⟨y, z, x, by rw [← h]; ring, by tauto⟩

/-- Solubility is preserved when the coefficients are multiplied by the same nonzero element. -/
theorem iff_scale [IsDomain R] {a b c d : R} (hd : d ≠ 0) :
    IsSoluble a b c ↔ IsSoluble (d * a) (d * b) (d * c) := by
  refine ⟨fun ⟨x, y, z, h, hnt⟩ ↦ ⟨x, y, z, ?_, hnt⟩, fun ⟨x, y, z, h, hnt⟩ ↦ ⟨x, y, z, ?_, hnt⟩⟩
  · apply_fun (d * ·) at h
    simpa only [mul_add, mul_assoc, mul_zero] using h
  · apply_fun (d * ·) using mul_right_injective₀ hd
    simpa only [mul_add, mul_assoc, mul_zero] using h

/-- Solubility is preserved when the coefficients are multiplied by a unit. -/
theorem iff_scale' {a b c d : R} (hd : IsUnit d) :
    IsSoluble a b c ↔ IsSoluble (d * a) (d * b) (d * c) := by
  refine ⟨fun ⟨x, y, z, h, hnt⟩ ↦ ⟨x, y, z, ?_, hnt⟩, fun ⟨x, y, z, h, hnt⟩ ↦ ⟨x, y, z, ?_, hnt⟩⟩
  · apply_fun (d * ·) at h
    simpa only [mul_add, mul_assoc, mul_zero] using h
  · apply_fun (d * ·) using hd.mul_right_injective
    simpa only [mul_add, mul_assoc, mul_zero] using h

/-- Solubility is preserved when the coefficients are negated. -/
theorem neg {a b c : R} (h : IsSoluble a b c) : IsSoluble (-a) (-b) (-c) := by
  rw [← neg_one_mul a, ← neg_one_mul b, ← neg_one_mul c]
  exact (iff_scale' isUnit_neg_one).mp h

theorem mul_mul_iff_mul [IsDomain R] {a b c d : R} (hd : d ≠ 0) :
    IsSoluble (a * d) (b * d) c ↔ IsSoluble a b (c * d) := by
  refine ⟨fun ⟨x, y, z, h, h₀⟩ ↦ ⟨d * x, d * y, z, ?_⟩,
    fun ⟨x, y, z, h, h₀⟩ ↦ ⟨x, y, d * z, ?_⟩⟩ <;>
    ( constructor
      · rw [← mul_eq_zero_of_right d h]
        ring
      · simpa only [ne_eq, mul_eq_zero, hd, false_or] using h₀ )

theorem mul_mul_iff_mul' {a b c d : R} (hd : IsUnit d) :
    IsSoluble (a * d) (b * d) c ↔ IsSoluble a b (c * d) := by
  have H (x : R) : d * x ≠ 0 ↔ x ≠ 0 :=
    ⟨right_ne_zero_of_mul, fun h hf ↦ h <| hd.mul_right_eq_zero.mp hf⟩
  refine ⟨fun ⟨x, y, z, h, h₀⟩ ↦ ⟨d * x, d * y, z, ?_⟩,
    fun ⟨x, y, z, h, h₀⟩ ↦ ⟨x, y, d * z, ?_⟩⟩ <;>
      ( constructor
        · rw [← mul_eq_zero_of_right d h]
          ring
        · simpa only [H, ne_eq] using h₀ )

theorem iff_mul_sq [IsDomain R] {a b c d : R} (hd : d ≠ 0) :
    IsSoluble a b (c * d ^ 2) ↔ IsSoluble a b c := by
  refine ⟨fun ⟨x, y, z, h, h₀⟩ ↦ ⟨x, y, d * z, by rw [← h]; ring, ?_⟩,
    fun ⟨x, y, z, h, h₀⟩ ↦ ⟨d * x, d * y, z, ?_, ?_⟩⟩
  · simpa only [ne_eq, mul_eq_zero, hd, false_or] using h₀
  · rw [← mul_eq_zero_of_right (d ^ 2) h]
    ring
  · simpa only [ne_eq, mul_eq_zero, hd, false_or] using h₀

theorem iff_mul_sq' {a b c d : R} (hd : IsUnit d) :
    IsSoluble a b (c * d ^ 2) ↔ IsSoluble a b c := by
  have H (x : R) : d * x ≠ 0 ↔ x ≠ 0 :=
    ⟨right_ne_zero_of_mul, fun h hf ↦ h <| hd.mul_right_eq_zero.mp hf⟩
  refine ⟨fun ⟨x, y, z, h, h₀⟩ ↦ ⟨x, y, d * z, by rw [← h]; ring, ?_⟩,
    fun ⟨x, y, z, h, h₀⟩ ↦ ⟨d * x, d * y, z, ?_, ?_⟩⟩
  · simpa only [ne_eq, H] using h₀
  · rw [← mul_eq_zero_of_right (d ^ 2) h]
    ring
  · simpa only [H, ne_eq] using h₀

end IsSoluble

end General

namespace IsSoluble

/-- If an integral triple is soluble, then there is a solution in coprime integers. -/
theorem primitive {a b c : ℤ} (h : IsSoluble a b c) :
    ∃ x y z, a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0 ∧ x.gcd (y.gcd z) = 1 := by
  obtain ⟨x, y, z, h, hnt⟩ := h
  obtain ⟨g, x₁, y₁, z₁, -, rfl, rfl, rfl, hg'⟩ := Int.exists_gcd_gcd_eq_one x y z
  have hg₀ : g ≠ 0 := by
    rintro rfl
    simp only [zero_mul, ne_eq, not_true_eq_false, or_self] at hnt
  refine ⟨x₁, y₁, z₁, eq_zero_of_ne_zero_of_mul_left_eq_zero (pow_ne_zero 2 hg₀) ?_, hg'⟩
  rw [← h]
  ring


/-!
### Assumptions on the coefficients and Legendre's conditions
-/

/-- This is the assumption on the coefficients in Legendre's Theorem:
they are coprime in pairs and squarefree. -/
def CoeffAss (a b c : ℤ) : Prop :=
  IsCoprime a b ∧ IsCoprime b c ∧ IsCoprime c a ∧ Squarefree a ∧ Squarefree b ∧ Squarefree c

namespace CoeffAss

/-- The assumptions are preserved when the first two coefficients are swapped. -/
theorem swap₁₂ {a b c : ℤ} (h : CoeffAss a b c) : CoeffAss b a c := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  exact ⟨h₁.symm, h₃.symm, h₂.symm, h₅, h₄, h₆⟩

/-- The assumptions are preserved when the first and the last coefficient are swapped. -/
theorem swap₁₃ {a b c : ℤ} (h : CoeffAss a b c) : CoeffAss c b a := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  exact ⟨h₂.symm, h₁.symm, h₃.symm, h₆, h₅, h₄⟩

/-- The assumptions are preserved when the coefficients are rotated. -/
theorem rotate {a b c : ℤ} (h : CoeffAss a b c) : CoeffAss b c a := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  exact ⟨h₂, h₃, h₁, h₅, h₆, h₄⟩

theorem neg_last {a b c : ℤ} (h : CoeffAss a b c) : CoeffAss a b (-c) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  exact ⟨h₁, h₂.neg_right, h₃.neg_left, h₄, h₅, h₆.neg⟩

theorem neg_all {a b c : ℤ} (h : CoeffAss a b c) : CoeffAss (-a) (-b) (-c) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  exact ⟨h₁.neg_neg, h₂.neg_neg, h₃.neg_neg, h₄.neg, h₅.neg, h₆.neg⟩

private lemma primitive'_help₂ {a b c x y z : ℤ} (h : CoeffAss a b c)
    (hs : a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0) (hg : x.gcd (y.gcd z) = 1) : IsCoprime x y := by
  rw [← Int.gcd_eq_one_iff_coprime, Nat.eq_one_iff_not_exists_prime_dvd]
  intro p hp hf
  replace hf := Int.natCast_dvd_natCast.mpr hf
  obtain ⟨x₁, rfl⟩ : ↑p ∣ x := hf.trans Int.gcd_dvd_left
  obtain ⟨y₁, rfl⟩ : ↑p ∣ y := hf.trans Int.gcd_dvd_right
  rw [add_eq_zero_iff_neg_eq,
    show -(a * (p * x₁) ^ 2 + b * (p * y₁) ^ 2) = p * (p * -(a * x₁ ^ 2 + b * y₁ ^ 2)) by ring]
    at hs
  have hpcz : ↑p ∣ c * z ^ 2 := dvd_of_mul_right_eq _ hs
  have hpz : ¬↑p ∣ z := by
    rintro ⟨z₁, rfl⟩
    rw [Int.gcd_mul_left, Int.natAbs_ofNat, Nat.cast_mul, Int.gcd_mul_left, Int.natAbs_ofNat] at hg
    exact hp.ne_one <| Nat.eq_one_of_mul_eq_one_right hg
  obtain ⟨c₁, rfl⟩ := (Int.Prime.dvd_mul' hp hpcz).resolve_right
    (fun hpz₂ ↦ hpz (Int.Prime.dvd_pow' hp hpz₂))
  rw [mul_assoc] at hs
  replace hs := (mul_right_inj' (show (p : ℤ) ≠ 0 from mod_cast hp.ne_zero)).mp hs
  have hpc₁z : ↑p ∣ c₁ * z ^ 2 := dvd_of_mul_right_eq _ hs
  obtain ⟨c₂, rfl⟩ := (Int.Prime.dvd_mul' hp hpc₁z).resolve_right
    (fun hpz₂' ↦ hpz (Int.Prime.dvd_pow' hp hpz₂'))
  replace h := h.2.2.2.2.2
  rw [← mul_assoc] at h
  exact (Nat.prime_iff_prime_int.mp hp).not_unit (h p <| dvd_mul_right ((p : ℤ) * p) c₂)

private lemma primitive'_help₁ {a b c x y z : ℤ} (h : CoeffAss a b c)
    (hs : a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0) (hg : x.gcd (y.gcd z) = 1) : IsCoprime a y := by
  rw [← Int.gcd_eq_one_iff_coprime, Nat.eq_one_iff_not_exists_prime_dvd]
  intro p hp hf
  replace hf := Int.natCast_dvd_natCast.mpr hf
  have hyz : IsCoprime y z := by
    rw [add_rotate] at hs
    rw [Int.gcd_comm, Int.gcd_assoc] at hg
    exact primitive'_help₂ h.rotate hs hg
  obtain ⟨a₁, rfl⟩ : ↑p ∣ a := hf.trans Int.gcd_dvd_left
  obtain ⟨y₁, rfl⟩ : ↑p ∣ y := hf.trans Int.gcd_dvd_right
  rw [add_eq_zero_iff_neg_eq,
    show -(p * a₁ * x ^ 2 + b * (p * y₁) ^ 2) = p * -(a₁ * x ^ 2 + p * (b * y₁ ^ 2)) by ring] at hs
  have hpcz : ↑p  ∣ c * z ^ 2 := dvd_of_mul_right_eq _ hs
  rcases Int.Prime.dvd_mul' hp hpcz with ⟨c₁, rfl⟩ | hpz₂
  · exact Int.not_isCoprime_of_mul_prime hp _ _ h.2.2.1
  · obtain ⟨z₁, rfl⟩ := Int.Prime.dvd_pow' hp hpz₂
    exact Int.not_isCoprime_of_mul_prime hp _ _ hyz

theorem primitive'_help {a b c x y z : ℤ} (h : CoeffAss a b c)
    (hs : a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0) (hg : x.gcd (y.gcd z) = 1) :
    IsCoprime (a * x) (b * y) := by
  refine IsCoprime.mul_left ?_ ?_ <;> refine IsCoprime.mul_right ?_ ?_
  · exact h.1
  · exact primitive'_help₁ h hs hg
  · rw [add_comm (a * _)] at hs
    rw [Int.gcd_comm, Int.gcd_assoc, Int.gcd_comm z] at hg
    exact (primitive'_help₁ h.swap₁₂ hs hg).symm
  · exact primitive'_help₂ h hs hg

end CoeffAss

open CoeffAss in
/-- If a coefficient triple `(a,b,c)` is soluble and satisfies `CoeffAss`, then there is
a solution `(x,y,z)` such that `a*x`, `b*y` and `c*z` are coprime in pairs. -/
theorem primitive' {a b c : ℤ} (h : IsSoluble a b c) (h' : CoeffAss a b c) :
    ∃ x y z,
      a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0 ∧
        IsCoprime (a * x) (b * y) ∧ IsCoprime (b * y) (c * z) ∧ IsCoprime (c * z) (a * x) := by
  obtain ⟨x, y, z, hs, hg⟩ := h.primitive
  refine ⟨x, y, z, hs, primitive'_help h' hs hg, ?_, ?_⟩
  · rw [add_rotate] at hs
    rw [Int.gcd_comm, Int.gcd_assoc] at hg
    exact primitive'_help h'.rotate hs hg
  · rw [← add_rotate] at hs
    rw [← Int.gcd_assoc, Int.gcd_comm] at hg
    exact primitive'_help h'.rotate.rotate hs hg

/-- This is the first solubility condition in Legendre's Theorem: the coefficients
do not all have the same sign. -/
def Condition₁ (a b c : ℤ) : Prop :=
  ¬(0 < a ∧ 0 < b ∧ 0 < c) ∧ ¬(a < 0 ∧ b < 0 ∧ c < 0)

theorem condition₁_iff {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    Condition₁ a b c ↔
      0 < a ∧ 0 < b ∧ c < 0 ∨ 0 < a ∧ b < 0 ∧ 0 < c ∨ a < 0 ∧ 0 < b ∧ 0 < c ∨
        a < 0 ∧ b < 0 ∧ 0 < c ∨ a < 0 ∧ 0 < b ∧ c < 0 ∨ 0 < a ∧ b < 0 ∧ c < 0 := by
  dsimp only [Condition₁]
  rcases ha.lt_or_lt with ha₁ | ha₁ <;>
    simp only [asymm ha₁, false_and, not_false_eq_true, ha₁, true_and, not_and, not_lt, or_false,
      false_or, not_and, and_true] <;>
    rcases hb.lt_or_lt with hb₁ | hb₁ <;>
    simp only [asymm hb₁, le_iff_eq_or_lt, hc, false_or, false_implies, false_and, hb₁, true_and,
      lt_or_lt_iff_ne, ne_eq, hc.symm, not_false_eq_true, or_true, hc.symm, true_implies, or_false]

/-- This is the second solubility condition in Legendre's theorem: the negative product
of each pair of coefficients is a square modulo the third. -/
def Condition₂ (a b c : ℤ) : Prop :=
  IsSquareMod (-b * c) a ∧ IsSquareMod (-a * c) b ∧ IsSquareMod (-a * b) c

theorem Condition₂.rotate {a b c : ℤ} (h : Condition₂ a b c) : Condition₂ b c a := by
  have H : ∀ x y : ℤ, -x * y = -y * x := fun x y ↦ by ring
  obtain ⟨ha, hb, hc⟩ := h
  rw [H] at hb hc
  exact ⟨hb, hc, ha⟩

theorem Condition₂.neg {a b c : ℤ} (h : Condition₂ a b c) : Condition₂ (-a) (-b) (-c) := by
  have H : ∀ x y : ℤ, - -x * -y = -x * y := fun x y ↦ by ring
  obtain ⟨ha, hb, hc⟩ := h
  rw [← IsSquareMod.neg_iff, ← H] at ha hb hc
  exact ⟨ha, hb, hc⟩

/-!
### The conditions are necessary
-/

-- The first condition in Legendre's Theorem is necessary.
private lemma necessary₁ {a b c : ℤ} (h : IsSoluble a b c) : ¬(0 < a ∧ 0 < b ∧ 0 < c) := by
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

-- The second condition in Legendre's Theorem is necessary.
private lemma necessary₂ {a b c : ℤ} (h : IsSoluble a b c) (h' : CoeffAss a b c) :
    IsSquareMod (-b * c) a := by
  obtain ⟨x, y, z, h, haxby, hbycz, hczax⟩ := h.primitive' h'
  rw [add_eq_zero_iff_eq_neg] at h
  replace h : -b * c * z ^ 2 - (b * y) ^ 2 = a * (b * x ^ 2) := by linear_combination b * h.symm
  have H : IsSquareMod (-b * c * z ^ 2) a := ⟨b * y, _, h⟩
  exact H.of_mul_sq_of_coprime_left hczax.symm.of_mul_right_right.of_mul_left_left

/-- The conditions in Legendre's Theorem are necessary. -/
theorem necessary {a b c : ℤ} (h : IsSoluble a b c) (h' : CoeffAss a b c) :
    Condition₁ a b c ∧ Condition₂ a b c :=
  ⟨⟨necessary₁ h, by simpa only [not_and, not_lt, Left.neg_pos_iff] using necessary₁ h.neg⟩,
    ⟨necessary₂ h h', necessary₂ h.swap₁₂ h'.swap₁₂, necessary₂ h.rotate.rotate h'.rotate.rotate⟩⟩


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
theorem of_equal {b : ℤ} (hb : 0 < b) (h : IsSquareMod (-1) b) : IsSoluble b b (-1) := by
  obtain ⟨r, s, hrs⟩ := h.sum_of_squares hb.le
  exact ⟨r, s, r ^ 2 + s ^ 2, by rw [hrs]; ring, .inr <| .inr <| hrs ▸ hb.ne'⟩

/-- This lemma is used to reduce the statement for `a` and `b` to the statement for `A` and `b`
with some `0 < A < a`. -/
theorem descent {a b : ℤ} (hb : 0 < b) (hba : b < a) (h : IsSquareMod b a) :
    ∃ A c m : ℤ, c ^ 2 - b = a * (m ^ 2 * A) ∧ Squarefree A ∧ 0 < A ∧ A < a := by
  obtain ⟨c, t, h₁, h₂, h₃⟩ := h.exists_le_half (hb.trans hba)
  rcases (show t ≤ 0 by nlinarith).eq_or_lt with rfl | htn
  · change 1 ≤ b at hb
    exact ⟨1, c, 0, by linear_combination -h₁, squarefree_one, zero_lt_one, hb.trans_lt hba⟩
  obtain ⟨A, m, ht, hA⟩ := Int.sq_mul_squarefree (-t)
  have hA₀ : 0 < A := pos_of_mul_pos_right (by rwa [ht, neg_pos]) (sq_nonneg m)
  refine ⟨A, c, m, by linear_combination -h₁ -a * ht, hA, hA₀, ?_⟩
  replace h₃ : 2 * c ≤ a :=
    ((mul_le_mul_left zero_lt_two).mpr h₃).trans (Int.mul_ediv_le zero_lt_two a)
  have H : a * (4 * m ^ 2 * A) < a * a :=
    calc a * (4 * m ^ 2 * A)
      _ = (2 * c) ^ 2 - 4 * b := by linear_combination 4 * h₁ + 4 * a * ht
      _ < (2 * c) ^ 2 := Int.sub_lt_self _ (mul_pos zero_lt_four hb)
      _ ≤ a ^ 2 := sq_le_sq' (by linarith [hb, hba, h₂]) h₃
      _ = a * a := sq a
  have hm₀ : m ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, zero_mul, eq_comm, neg_eq_zero] at ht
    exact htn.ne ht
  calc A
    _ = 1 * A := (one_mul A).symm
    _ ≤ 4 * m ^ 2 * A := mul_le_mul_of_nonneg_right (by change 0 < 4 * m ^ 2; positivity) hA₀.le
    _ < a := lt_of_mul_lt_mul_left H (hb.trans hba).le

/-- This shows that the first condition, `IsSquareMod a b` is preserved when we replace `a`
by `A` (as obtained from `Legendre.IsSoluble.descent`). -/
theorem condition_i {A a b c m : ℤ} (sa : Squarefree a) (sb : Squarefree b) (h₁ : IsSquareMod a b)
    (h₃ : IsSquareMod (-a * b / (a.gcd b : ℤ) ^ 2) (a.gcd b : ℤ))
    (h' : c ^ 2 - b = a * (m ^ 2 * A)) :
    IsSquareMod A b := by
  obtain ⟨g, a₁, b₁, c₁, hg, rfl, rfl, rfl, h⟩ := Int.exists_gcd_gcd_eq_one a b c
  have hg₀ : g ≠ 0 := left_ne_zero_of_mul sa.ne_zero
  have hag := Int.isCoprime_of_squarefree_mul sa
  have hbg := Int.isCoprime_of_squarefree_mul sb
  replace h' : g * (c₁ ^ 2 * g - b₁) = g * (a₁ * (m ^ 2 * A)) := by linear_combination h'
  replace h' := mul_left_cancel₀ hg₀ h'
  have hg₁ : IsCoprime a₁ b₁ := by
    by_contra hf
    obtain ⟨p, hp, ⟨a₁, rfl⟩, ⟨b₁, rfl⟩⟩ := Int.not_isCoprime_iff_exists_prime_dvd.mp hf
    have H : ↑p ∣ c₁ ^ 2 * g := ⟨b₁ + a₁ * (m ^ 2 * A), by linear_combination h'⟩
    obtain ⟨c₁, rfl⟩ := Int.Prime.dvd_pow' hp (hbg.of_mul_right_left.symm.dvd_of_dvd_mul_right H)
    simp only [Int.gcd_mul_left, Nat.cast_mul, Int.natAbs_ofNat] at h
    exact hp.not_dvd_one <| dvd_of_mul_right_eq _ h
  rw [Int.gcd_mul_left, Int.gcd_eq_one_iff_coprime.mpr hg₁, mul_one, Int.natAbs_sq,
    ← IsSquareMod.iff_natAbs, (by ring : -(g * a₁) * (g * b₁) = -a₁ * b₁ * g ^ 2),
    Int.mul_ediv_cancel _ (pow_ne_zero 2 hg₀)] at h₃
  refine IsSquareMod.mul_of_coprime ?_ ?_ hbg
  · have H := hbg.neg_right.mul_add_right_right (c₁ ^ 2)
    rw [← sub_eq_add_neg, h', sq, ← mul_assoc, mul_comm a₁, mul_assoc, mul_assoc] at H
    replace h' : g * (a₁ * c₁ ^ 2) = A * (a₁ * m) ^ 2 - -a₁ * b₁ := by linear_combination a₁ * h'
    exact
      (h₃.of_dvd_sub ⟨_, h'.symm⟩).of_mul_sq_of_coprime_left (hag.mul_right H.of_mul_right_left)
  · have ha := hbg.mul_left hg₁
    have hsm : IsSquareMod (g * a₁ * (m ^ 2 * A)) b₁ := ⟨c₁ * g, -g, by linear_combination -g * h'⟩
    have hm : IsCoprime b₁ m := by
      by_contra hf
      obtain ⟨p, hp, ⟨b₂, rfl⟩, ⟨m', rfl⟩⟩ := Int.not_isCoprime_iff_exists_prime_dvd.mp hf
      rw [sub_eq_iff_eq_add] at h'
      have H : ↑p ∣ c₁ ^ 2 * g := ⟨a₁ * p * m' ^ 2 * A + b₂, by linear_combination h'⟩
      obtain ⟨c₂, rfl⟩ := Int.Prime.dvd_pow' hp (hbg.symm.of_mul_left_left.dvd_of_dvd_mul_right H)
      obtain ⟨b₃, rfl⟩ : ↑p ∣ b₂ := by
        refine ⟨c₂ ^ 2 * g - a₁ * m' ^ 2 * A, ?_⟩
        apply_fun ((p : ℤ) * ·) using mul_right_injective₀ (Nat.cast_ne_zero.mpr hp.ne_zero)
        linear_combination -h'
      exact hp.not_unit (Int.ofNat_isUnit.mp <| sb p ⟨b₃ * g, by ring⟩)
    exact (hsm.of_mul h₁.of_mul_right ha).of_mul_sq_of_coprime_right hm

/-- This shows that the third condition, `IsSquareMod (-a*b/(a.gcd b)^2) (a.gcd b)`
is preserved when we replace `a` by `A` (as obtained from `Legendre.IsSoluble.descent`). -/
theorem condition_iii {A a b c m : ℤ} (sb : Squarefree b) (h₁ : IsSquareMod a b)
    (h' : c ^ 2 - b = a * (m ^ 2 * A)) :
    IsSquareMod (-A * b / (A.gcd b : ℤ) ^ 2) (A.gcd b : ℤ) := by
  obtain ⟨g, A₁, b₁, c₁, hg, rfl, rfl, rfl, h⟩ := Int.exists_gcd_gcd_eq_one A b c
  have hg₀ : g ≠ 0 := left_ne_zero_of_mul sb.ne_zero
  have hbg := Int.isCoprime_of_squarefree_mul sb
  replace h' : g * (c₁ ^ 2 * g - b₁) = g * (a * (m ^ 2 * A₁)) := by linear_combination h'
  replace h' := mul_left_cancel₀ hg₀ h'
  have hg₁ : IsCoprime A₁ b₁ := by
    -- maybe prove a lemma; see similar statement above
    by_contra hf
    obtain ⟨p, hp, ⟨A₂, rfl⟩, ⟨b₂, rfl⟩⟩ := Int.not_isCoprime_iff_exists_prime_dvd.mp hf
    have H : ↑p ∣ c₁ ^ 2 * g := ⟨b₂ + a * (m ^ 2 * A₂), by linear_combination h'⟩
    obtain ⟨c₂, rfl⟩ := Int.Prime.dvd_pow' hp (hbg.of_mul_right_left.symm.dvd_of_dvd_mul_right H)
    simp only [Int.gcd_mul_left, Nat.cast_mul, Int.natAbs_ofNat] at h
    exact hp.not_dvd_one <| dvd_of_mul_right_eq _ h
  rw [Int.gcd_mul_left, Int.gcd_eq_one_iff_coprime.mpr hg₁, mul_one, Int.natAbs_sq,
    ← IsSquareMod.iff_natAbs, show -(g * A₁) * (g * b₁) = -A₁ * b₁ * g ^ 2 by ring,
    Int.mul_ediv_cancel _ (pow_ne_zero 2 hg₀)]
  obtain ⟨u, v, huv⟩ := h₁.of_mul_left
  exact ⟨u * m * A₁, A₁ * (v * m ^ 2 * A₁ - c₁ ^ 2),
    by linear_combination A₁ * h' + A₁ ^ 2 * m ^ 2 * huv⟩

/-- If we have a solution for `A` and `b` (with `A` obtained from `Legendre.IsSoluble.descent`),
then there is also a solution for `a` and `b`. -/
theorem transfer {A a b c m : ℤ} (hm : m ≠ 0) (hA : A ≠ 0) (ha : a ≠ 0)
    (h : IsSoluble A b (-1)) (h' : c ^ 2 - b = a * (m ^ 2 * A)) : IsSoluble a b (-1) := by
  obtain ⟨x, y, z, h, hnt⟩ := h
  refine ⟨m * A * x, c * y + z, b * y + c * z,
    by linear_combination a * m ^ 2 * A * h + (b * y ^ 2 - z ^ 2) * h', ?_⟩
  by_contra! hf
  obtain ⟨h₁, h₂, h₃⟩ := hf
  have hy : (c ^ 2 - b) * y = 0 := by linear_combination c * h₂ - h₃
  have hz : (c ^ 2 - b) * z = 0 := by linear_combination -b * h₂ + c * h₃
  have hcb : c ^ 2 - b ≠ 0 := h' ▸ mul_ne_zero ha (mul_ne_zero (pow_ne_zero 2 hm) hA)
  rcases hnt with hx' | hy' | hz'
  · exact hx' (eq_zero_of_ne_zero_of_mul_left_eq_zero (mul_ne_zero hm hA) h₁)
  · exact hy' (eq_zero_of_ne_zero_of_mul_left_eq_zero hcb hy)
  · exact hz' (eq_zero_of_ne_zero_of_mul_left_eq_zero hcb hz)

/-- This shows the variant of Legendre's Theorem under the additional assumption that `b < a`. -/
theorem neg_one_of_lt {a b : ℤ} (sa : Squarefree a) (sb : Squarefree b) (hb : 0 < b)
    (hba : b < a) (h₁ : IsSquareMod a b) (h₂ : IsSquareMod b a)
    (h₃ : IsSquareMod (-a * b / (a.gcd b : ℤ) ^ 2) (a.gcd b : ℤ)) : IsSoluble a b (-1) := by
  lift b to ℕ using hb.le
  lift a to ℕ using (hb.trans hba).le
  induction' a using Nat.strong_induction_on with a ih generalizing b
  obtain ⟨A, c, m, h', sf, hA, hAa⟩ := descent hb hba h₂
  rcases eq_or_ne m 0 with rfl | hm
  · exact ⟨0, 1, c, by linear_combination -h', .inr (.inl one_ne_zero)⟩
  have b₁ := condition_i sa sb h₁ h₃ h'
  have b₂ : IsSquareMod (b : ℤ) A := ⟨c, -a * m ^ 2, by linear_combination -h'⟩
  have b₃ := condition_iii sb h₁ h'
  lift A to ℕ using hA.le
  refine transfer hm sf.ne_zero sa.ne_zero ?_ h'
  rcases lt_trichotomy A b with hAb | rfl | hAb
  · rw [neg_mul, mul_comm, ← neg_mul, Int.gcd_comm] at b₃
    exact (ih b (Nat.cast_lt.mp hba) _ sf hA sb (Nat.cast_lt.mpr hAb) b₂ b₁ b₃).swap₁₂
  · rw [neg_mul, Int.gcd_self, Int.natAbs_ofNat, ← sq, Int.neg_ediv_of_dvd (Int.dvd_refl _),
        Int.ediv_self (sq_pos_of_ne_zero hb.ne').ne'] at b₃
    exact of_equal hb b₃
  · exact ih A (Nat.cast_lt.mp hAa) _ sb hb sf (Nat.cast_lt.mpr hAb) b₁ b₂ b₃

/-- This is the (interesting direction of) the variant of Legendre's Theorem:
if `a` and `b` are positive and squarefree, `a` is a square modulo `b`, `b` is a square
modulo `a`, and `-a*b/(a.gcd b)^2` is a square modulo `a.gcd b`, then the equation
`a*x^2 + b*y^2 = z^2` has a nontrivial solution in integers. -/
theorem neg_one {a b : ℤ} (ha₀ : 0 < a) (hb₀ : 0 < b) (ha : Squarefree a)
    (hb : Squarefree b) (hab : IsSquareMod a b) (hba : IsSquareMod b a)
    (hd : IsSquareMod (-a * b / (a.gcd b : ℤ) ^ 2) (a.gcd b : ℤ)) : IsSoluble a b (-1) := by
  rcases lt_trichotomy a b with hab' | rfl | hab'
  · rw [neg_mul, mul_comm, ← neg_mul, Int.gcd_comm] at hd
    exact (neg_one_of_lt hb ha ha₀ hab' hba hab hd).swap₁₂
  · rw [neg_mul, Int.gcd_self, ← sq, Int.natAbs_sq, Int.neg_ediv_of_dvd ⟨1, (mul_one _).symm⟩,
      Int.ediv_self (sq_pos_of_ne_zero hb₀.ne').ne', ← Int.eq_natAbs_of_zero_le ha₀.le] at hd
    exact of_equal ha₀ hd
  · exact neg_one_of_lt ha hb hb₀ hab' hab hba hd


/-- This shows the sufficiency of the conditions in Legendre's Theorem when the first two
coefficients are positive and the last is negative. -/
theorem sufficient' {a b c : ℤ} (ha₁ : 0 < a) (hb₁ : 0 < b) (hc₁ : 0 < c) (h₂ : Condition₂ a b (-c))
    (h' : CoeffAss a b c) : IsSoluble a b (-c) := by
  obtain ⟨ha₂, hb₂, hc₂⟩ := h₂
  obtain ⟨hab, hbc, hca, ha, hb, hc⟩ := h'
  rw [neg_mul_neg] at ha₂ hb₂
  rw [IsSquareMod.neg_iff, neg_mul] at hc₂
  rw [show -c = -1 * c by simp only [neg_mul, one_mul], ← IsSoluble.mul_mul_iff_mul hc₁.ne']
  refine neg_one (mul_pos ha₁ hc₁) (mul_pos hb₁ hc₁)
    ((Int.squarefree_mul hca.symm).mpr ⟨ha, hc⟩) ((Int.squarefree_mul hbc).mpr ⟨hb, hc⟩)
    (hb₂.mul_of_coprime (isSquareMod_mul_self a c) hbc)
    (ha₂.mul_of_coprime (isSquareMod_mul_self b c) hca.symm) ?_
  have hg : ((a * c).gcd (b * c) : ℤ) = c := by
    rw [Int.gcd_mul_right, Int.gcd_eq_one_iff_coprime.mpr hab, one_mul, Int.natAbs_of_nonneg hc₁.le]
  rwa [hg, neg_mul, show a * c * (b * c) = a * b * c ^ 2 by ring, ← neg_mul,
    Int.mul_ediv_cancel _ (pow_ne_zero 2 hc₁.ne')]

/-- This shows that the conditions in Legendre's Theorem are sufficient. -/
theorem sufficient {a b c : ℤ} (h₁ : Condition₁ a b c) (h₂ : Condition₂ a b c)
    (h' : CoeffAss a b c) : IsSoluble a b c := by
  have h'' := h'
  obtain ⟨-, -, -, ha, hb, hc⟩ := h''
  rcases(condition₁_iff ha.ne_zero hb.ne_zero hc.ne_zero).mp h₁ with H | H | H | H | H | H
  · rw [← neg_neg c] at h₂ H ⊢
    exact sufficient' H.1 H.2.1 (neg_lt_zero.mp H.2.2) h₂ h'.neg_last
  · rw [← neg_neg b] at h₂ H ⊢
    exact sufficient' H.2.2 H.1 (neg_lt_zero.mp H.2.1) h₂.rotate.rotate
      h'.rotate.rotate.neg_last |>.rotate
  · rw [← neg_neg a] at h₂ H ⊢
    exact sufficient' H.2.1 H.2.2 (neg_lt_zero.mp H.1) h₂.rotate h'.rotate.neg_last
      |>.rotate.rotate
  · rw [← neg_neg a, ← neg_neg b] at H ⊢
    rw [← neg_neg c]
    simp_rw [neg_lt_zero] at H
    exact (sufficient' H.1 H.2.1 H.2.2 h₂.neg <| neg_neg c ▸ h'.neg_all.neg_last).neg
  · rw [← neg_neg a, ← neg_neg c] at H ⊢
    rw [← neg_neg b]
    simp_rw [neg_lt_zero] at H
    refine (IsSoluble.rotate <| sufficient' H.2.2 H.1 H.2.1 h₂.rotate.rotate.neg ?_).neg
    exact neg_neg b ▸ h'.rotate.rotate.neg_all.neg_last
  · rw [← neg_neg b, ← neg_neg c] at H ⊢
    rw [← neg_neg a]
    simp_rw [neg_lt_zero] at H
    refine
      (IsSoluble.rotate <| IsSoluble.rotate <| sufficient' H.2.1 H.2.2 H.1 h₂.rotate.neg ?_).neg
    exact neg_neg a ▸ h'.rotate.neg_all.neg_last

end IsSoluble

open IsSoluble

/-- The main result: *Legendre's Theorem* on ternary quadratic forms. Let `a`, `b`, `c`
be pairwise coprime and squarefree integers. Then the equation `a*x^2 + b*y^2 + c*z^2 = 0`
has a nontrivial solution in integers if and only if not all of `a`, `b`, `c` have the
same sign and `-a*b` is a square modulo `c`, `-b*c` is a square modulo `a` and
`-a*c` is a square modulo `b`.
-/
theorem isSoluble_iff {a b c : ℤ} (h : CoeffAss a b c) :
    IsSoluble a b c ↔ Condition₁ a b c ∧ Condition₂ a b c :=
  ⟨fun H ↦ necessary H h, fun H ↦ sufficient H.1 H.2 h⟩

end Legendre
