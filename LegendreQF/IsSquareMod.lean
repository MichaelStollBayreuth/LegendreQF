import Mathlib.NumberTheory.SumTwoSquares

/-!
# Squares modulo a ring element

We define a predicate `IsSquareMod a b` that expresses that `a` is congruent to a
square modulo `b`, where `a` and `b` are elements of a commutative ring `R`.

We then provide some API lemmas for it that are valid in general commutative rings.

Finally, we prove some more specific properties in the case that `R = ℤ`.
-/

section General

variable {R : Type*} [CommRing R]

/-- `IsSquareMod a b` means that the residue class of `a` modulo `b` is a square. -/
def IsSquareMod (a b : R) : Prop :=
  ∃ x, b ∣ a - x ^ 2

@[simp]
theorem isSquareMod_zero (m : R) : IsSquareMod (0 : R) m :=
  ⟨0, 0, by ring⟩

@[simp]
theorem isSquareMod_one (m : R) : IsSquareMod (1 : R) m :=
  ⟨1, 0, by ring⟩

@[simp]
theorem isSquareMod_sq (a m : R) : IsSquareMod (a ^ 2) m :=
  ⟨a, 0, by ring⟩

@[simp]
theorem isSquareMod_self (m : R) : IsSquareMod m m :=
  ⟨0, 1, by ring⟩

@[simp]
theorem isSquareMod_mul_self (a m : R) : IsSquareMod (a * m) m :=
  ⟨0, a, by ring⟩

@[simp]
theorem isSquareMod_self_mul (a m : R) : IsSquareMod (m * a) m :=
  ⟨0, a, by ring⟩

@[simp]
theorem isSquareMod_mod_one (a : R) : IsSquareMod a 1 :=
  ⟨0, a, by ring⟩

namespace IsSquareMod

/-- If `a` is a square modulo `m` and `m` divides `b - a`, then `b` is a square modulo `m`. -/
theorem of_dvd_sub {a b m : R} (h : IsSquareMod a m) (h' : m ∣ b - a) : IsSquareMod b m := by
  obtain ⟨u, h⟩ := h
  refine ⟨u, ?_⟩
  rw [show b - u ^ 2 = b - a + (a - u ^ 2) by ring]
  exact dvd_add h' h

/-- If `a` is a square modulo `m * n`, then `a` is a square modulo `m`. -/
theorem of_mul_left {a m n : R} (h : IsSquareMod a (m * n)) : IsSquareMod a m := by
  obtain ⟨b, c, h⟩ := h
  exact ⟨b, n * c, by rw [h, mul_assoc]⟩

/-- If `a` is a square modulo `m * n`, then `a` is a square modulo `n`. -/
theorem of_mul_right {a m n : R} (h : IsSquareMod a (m * n)) : IsSquareMod a n :=
  (mul_comm m n ▸ h).of_mul_left

/-- If `a` and `b` are both squares modulo `m`, then `a * b` is also a square modulo `m`. -/
theorem mul {a b m : R} (ha : IsSquareMod a m) (hb : IsSquareMod b m) :
    IsSquareMod (a * b) m := by
  obtain ⟨u, v, ha⟩ := ha
  obtain ⟨x, y, hb⟩ := hb
  exact ⟨u * x, u ^ 2 * y + x ^ 2 * v + m * v * y,
    by linear_combination b * ha + (u ^ 2 + m * v) * hb⟩

/-- If `a * b` and `a` are both squares modulo `m` and `a` is invertible modulo `m`,
then `b` is a square modulo `m`. -/
theorem of_mul {a b m : R} (hab : IsSquareMod (a * b) m) (ha : IsSquareMod a m)
    (h : IsCoprime a m) : IsSquareMod b m := by
  obtain ⟨u, v, hab⟩ := hab
  obtain ⟨x, y, ha⟩ := ha
  obtain ⟨r, s, hrs⟩ := h
  refine ⟨r * x * u, r ^ 2 * (x ^ 2 * v + y * u ^ 2 + m * y * v) + (2 * r * a + s * m) * s * b, ?_⟩
  linear_combination (r ^ 2 * x ^ 2 + r ^ 2 * m * y) * hab + (-(b * r * m * s) + b * r) * ha +
    (-(b * r * x ^ 2) - b * r * m * y - b * m * s - b) * hrs

/-- `a` is a square modulo `-m` if and only if it is a square modulo `m`. -/
@[simp]
theorem neg_iff {a m : R} : IsSquareMod a (-m) ↔ IsSquareMod a m := by
  refine ⟨fun ⟨u, v, h⟩ ↦ ?_, fun ⟨u, v, h⟩ ↦ ?_⟩ <;>
    exact ⟨u, -v, by rw [h]; ring⟩

/-- If `a` is a square modulo `m` and modulo `n` and `m` and `n` are coprime,
then `a` is a square modulo `m * n`. -/
theorem mul_of_coprime {a m n : R} (hm : IsSquareMod a m) (hn : IsSquareMod a n)
    (h : IsCoprime m n) : IsSquareMod a (m * n) := by
  obtain ⟨xm, ym, hm⟩ := hm
  obtain ⟨xn, yn, hn⟩ := hn
  obtain ⟨u, v, h⟩ := h
  refine ⟨v * n * xm + u * m * xn, v ^ 2 * n * ym + 2 * u * v * (a - xm * xn) + u ^ 2 * m * yn, ?_⟩
  linear_combination v ^ 2 * n ^ 2 * hm + u ^ 2 * m ^ 2 * hn + (-(a * v * n) - a * u * m - a) * h

/-- If `a^2 * b` is a square modulo `m` and `m` and `a` are coprime, then `b` is a square
modulo `m`. -/
theorem of_mul_sq_of_coprime_right {a b m : R} (hs : IsSquareMod (a ^ 2 * b) m)
    (hc : IsCoprime m a) : IsSquareMod b m :=
  hs.of_mul (isSquareMod_sq a m) hc.symm.pow_left

/-- If `a * b^2` is a square modulo `m` and `m` and `b` are coprime, then `a` is a square
modulo `m`. -/
theorem of_mul_sq_of_coprime_left {a b m : R} (hs : IsSquareMod (a * b ^ 2) m)
    (hc : IsCoprime m b) : IsSquareMod a m :=
  (mul_comm a _ ▸ hs).of_mul_sq_of_coprime_right hc

/-- If `a` is a square modulo `m`, `n` divides `m` and is coprime with `2 * a`, then
`a` is a square modulo `m * n`. -/
theorem mul_of_dvd_of_coprime {a m n : R} (hs : IsSquareMod a m) (hd : n ∣ m)
    (hc : IsCoprime n (2 * a)) : IsSquareMod a (m * n) := by
  obtain ⟨u, v, huv⟩ := hs
  obtain ⟨d, hd⟩ := hd
  obtain ⟨r, s, hrs⟩ := hc
  refine ⟨u * (1 + m * s * v), v * (r + d * s * v * (2 - s * u ^ 2)), ?_⟩
  linear_combination -m * v * hrs + (-(u ^ 2 * m * s ^ 2 * v ^ 2) + 2 * m * s * v ^ 2) * hd +
    (2 * m * s * v + 1) * huv

/-- If `a` is a square modulo `m` and `m` is coprime with `2 * a`, then `a` is a square
modulo any power of `m`. -/
theorem pow_of_coprime {a m : R} (hs : IsSquareMod a m) (hc : IsCoprime m (2 * a)) (n : ℕ) :
    IsSquareMod a (m ^ n) := by
  induction n with
  | zero => simp only [pow_zero, isSquareMod_mod_one]
  | succ n ih =>
    rw [pow_succ', mul_comm]
    cases n
    · simpa only [pow_zero, one_mul] using hs
    · exact ih.mul_of_dvd_of_coprime (dvd_pow (dvd_refl m) (Nat.zero_ne_add_one _).symm) hc

end IsSquareMod

end General

section Integer

/-!
### Squares modulo an integer
-/

namespace IsSquareMod

/-- If `a` is a square modulo `m > 0`, then there are `b` and `c` such that
`a - b ^ 2 = m * c` with `0 ≤ b ≤ m / 2`. -/
theorem exists_le_half {a m : ℤ} (hm : 0 < m) (h : IsSquareMod a m) :
    ∃ b c : ℤ, a - b ^ 2 = m * c ∧ 0 ≤ b ∧ b ≤ m / 2 := by
  obtain ⟨u, v, h⟩ := h
  rw [← Int.emod_add_ediv' u m] at h
  rcases le_or_lt (u % m) (m / 2) with hu | hu
  · exact ⟨u % m, v + 2 * (u % m) * (u / m) + (u / m) ^ 2 * m, by linear_combination h,
      u.emod_nonneg hm.ne', hu⟩
  · refine ⟨m - u % m, v - 2 * (m - u % m) * (1 + u / m) + (1 + u / m) ^ 2 * m,
      by linear_combination h, sub_nonneg.mpr (u.emod_lt_of_pos hm).le, ?_⟩
    nth_rewrite 1 [← Int.ediv_add_emod' m 2]
    rw [sub_le_iff_le_add, ← sub_le_iff_le_add',
      show m / 2 * 2 + m % 2 - m / 2 = m / 2 + m % 2 by ring]
    change m / 2 + 1 ≤ u % m at hu
    have H : m % 2 ≤ 1 := Int.lt_add_one_iff.mp (m.emod_lt_of_pos zero_lt_two)
    exact (add_le_add_left H (m / 2)).trans hu

/-- `a` is a square modulo `m` if and only if it is a square modulo `m.natAbs`. -/
theorem iff_natAbs {a m : ℤ} : IsSquareMod a m ↔ IsSquareMod a m.natAbs := by
  rcases Int.natAbs_eq m with h | h <;> nth_rw 1 [h]
  exact neg_iff

/-- `IsSquareMod a m` is equivalent with `IsSquare (a : ZMod m.natAbs)`. -/
theorem iff_isSquare (a m : ℤ) : IsSquareMod a m ↔ IsSquare (a : ZMod m.natAbs) := by
  refine ⟨fun ⟨b, h⟩ ↦ ⟨(b : ZMod m.natAbs), ?_⟩, fun ⟨b, h⟩ ↦ ⟨b.valMinAbs, ?_⟩⟩
  · rwa [← sq, ← Int.cast_pow, ← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd,
      Int.natCast_natAbs, abs_dvd]
  · rw [← ZMod.coe_valMinAbs b, ← sq, ← Int.cast_pow, ← sub_eq_zero, ← Int.cast_sub] at h
    rwa [← abs_dvd, ← Int.natCast_natAbs, ← ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- If `m` is a natural number, then `IsSquareMod a m` is equivalent with
`IsSquare (a : ZMod m)`. -/
theorem iff_isSquare' (a : ℤ) (m : ℕ) : IsSquareMod a m ↔ IsSquare (a : ZMod m) :=
  IsSquareMod.iff_isSquare a m

/-- `-1` is a square modulo a prime `p` if and only if `p % 4 ≠ 3`. -/
theorem iff_not_three_mod_four (p : ℕ) [Fact p.Prime] : IsSquareMod (-1 : ℤ) p ↔ p % 4 ≠ 3 := by
  rw [IsSquareMod.iff_isSquare', Int.cast_neg, Int.cast_one]
  exact ZMod.exists_sq_eq_neg_one_iff

/-- If `-1` is a square mod `b` and `0 ≤ b`, then `b` is a sum of two squares. -/
theorem sum_of_squares {b : ℤ} (hb : 0 ≤ b) (h : IsSquareMod (-1) b) :
    ∃ x y : ℤ, b = x ^ 2 + y ^ 2 := by
  lift b to ℕ using hb
  replace h : IsSquare (-1 : ZMod b) := by
    rw [show (-1 : ZMod b) = (-1 : ℤ) by norm_cast]
    exact (iff_isSquare' (-1) b).mp h
  obtain ⟨x, y, hxy⟩ := Nat.eq_sq_add_sq_of_isSquare_mod_neg_one h
  exact ⟨x, y, by exact_mod_cast hxy⟩

end IsSquareMod

end Integer
