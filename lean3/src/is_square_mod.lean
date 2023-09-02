import auxiliary
import number_theory.sum_two_squares
-- import tactic.polyrith

/-!
# Squares modulo a ring element

We define a predicate `is_square_mod a b` that expresses that `a` is congruent to a
square modulo `b`, where `a` and `b` are elements of a commutative ring `R`.

We then provide some API lemmas for it that are valid in general commutative rings.

Finally, we prove some more specific properties in the case that `R = ℤ`.
-/

section general

variables {R : Type*} [comm_ring R]

/-- `is_square_mod a b` means that the residue class of `a` modulo `b` is a square. -/
def is_square_mod (a b : R) : Prop := ∃ x, b ∣ a - x ^ 2

@[simp] lemma is_square_mod_zero (m : R) : is_square_mod (0 : R) m := ⟨0, 0, by ring⟩

@[simp] lemma is_square_mod_one (m : R) : is_square_mod (1 : R) m := ⟨1, 0, by ring⟩

@[simp] lemma is_square_mod_sq (a m : R) : is_square_mod (a ^ 2) m := ⟨a, 0, by ring⟩

@[simp] lemma is_square_mod_self (m : R) : is_square_mod m m := ⟨0, 1, by ring⟩

@[simp] lemma is_square_mod_mul_self (a m : R) : is_square_mod (a * m) m := ⟨0, a, by ring⟩

@[simp] lemma is_square_mod_self_mul (a m : R) : is_square_mod (m * a) m := ⟨0, a, by ring⟩

@[simp] lemma is_square_mod_mod_one (a : R) : is_square_mod a 1 := ⟨0, a, by ring⟩

namespace is_square_mod

/-- If `a` is a square modulo `m` and `m` divides `b - a`, then `b` is a square modulo `m`. -/
lemma of_dvd_sub {a b m : R} (h : is_square_mod a m) (h' : m ∣ b - a) : is_square_mod b m :=
begin
  obtain ⟨u, h⟩ := h,
  refine ⟨u, _⟩,
  rw show b - u ^ 2 = b - a + (a - u ^ 2), from by ring,
  exact dvd_add h' h,
end

/-- If `a` is a square modulo `m*n`, then `a` is a square modulo `m`. -/
lemma of_mul_left {a m n : R} (h : is_square_mod a (m * n)) : is_square_mod a m :=
begin
  obtain ⟨b, c, h⟩ := h,
  refine ⟨b, n * c, _⟩,
  rw [h, mul_assoc],
end

/-- If `a` is a square modulo `m*n`, then `a` is a square modulo `n`. -/
lemma of_mul_right {a m n : R} (h : is_square_mod a (m * n)) : is_square_mod a n :=
begin
  rw mul_comm at h,
  exact h.of_mul_left,
end

/-- If `a` and `b` are both squares modulo `m`, then `a*b` is also a square modulo `m`. -/
lemma mul {a b m : R} (ha : is_square_mod a m) (hb : is_square_mod b m) :
  is_square_mod (a * b) m :=
begin
  obtain ⟨u, v, ha⟩ := ha,
  obtain ⟨x, y, hb⟩ := hb,
  exact ⟨u * x, u ^ 2 * y + x ^ 2 * v + m * v * y,
         by linear_combination b * ha + (u ^ 2 + m * v) * hb⟩,
end

/-- If `a*b` and `a` are both squares modulo `m` and `a` is invertible modulo `m`,
then `b` is a square modulo `m`. -/
lemma of_mul {a b m : R} (hab : is_square_mod (a * b) m) (ha : is_square_mod a m)
  (h : is_coprime a m) : is_square_mod b m :=
begin
  obtain ⟨u, v, hab⟩ := hab,
  obtain ⟨x, y, ha⟩ := ha,
  obtain ⟨r, s, hrs⟩ := h,
  refine ⟨r * x * u, r ^ 2 * (x ^ 2 * v + y * u ^ 2 + m * y * v) + (2 * r * a + s * m) * s * b, _⟩,
  linear_combination (r ^ 2 * x ^ 2 + r ^ 2 * m * y) * hab + (-(b * r * m * s) + b * r) * ha
                       + (-(b * r * x ^ 2) - b * r * m * y - b * m * s - b) * hrs,
end

/-- `a` is a square modulo `m` if and only if it is a square modulo `-m`. -/
@[simp] lemma iff_neg {a m : R} : is_square_mod a (-m) ↔ is_square_mod a m :=
begin
  refine ⟨λ h, _, λ h, _⟩;
    { obtain ⟨u, v, h⟩ := h,
      exact ⟨u, -v, by {rw h, ring}⟩, }
end

/-- If `a` is a square modulo `m` and modulo `n` and `m` and `n` are coprime,
then `a` is a square modulo `m*n`. -/
lemma mul_of_coprime {a m n : R} (hm : is_square_mod a m) (hn : is_square_mod a n)
  (h: is_coprime m n) :
  is_square_mod a (m * n) :=
begin
  obtain ⟨xm, ym, hm⟩ := hm,
  obtain ⟨xn, yn, hn⟩ := hn,
  obtain ⟨u, v, h⟩ := h,
  refine ⟨v * n * xm + u * m * xn, v ^ 2 * n * ym + 2 * u * v * (a - xm * xn) + u ^ 2 * m * yn, _⟩,
  linear_combination v ^ 2 * n ^ 2 * hm + u ^ 2 * m ^ 2 * hn + (-(a * v * n) - a * u * m - a) * h,
end

/-- If `a^2 * b` is a square modulo `m` and `m` and `a` are coprime, then `b` is a square
modulo `m`. -/
lemma of_mul_sq_of_coprime_right {a b m : R} (hs : is_square_mod (a ^ 2 * b) m)
  (hc : is_coprime m a) : is_square_mod b m :=
hs.of_mul (is_square_mod_sq a m) hc.symm.pow_left

/-- If `a * b^2` is a square modulo `m` and `m` and `b` are coprime, then `a` is a square
modulo `m`. -/
lemma of_mul_sq_of_coprime_left {a b m : R} (hs : is_square_mod (a * b ^ 2) m)
  (hc : is_coprime m b) : is_square_mod a m :=
begin
  rw mul_comm at hs,
  exact hs.of_mul_sq_of_coprime_right hc,
end

/-- If `a` is a square modulo `m`, `n` divides `m` and is coprime with `2*a`, then
`a` is a square modulo `m*n`. -/
lemma mul_of_dvd_of_coprime {a m n : R} (hs : is_square_mod a m) (hd : n ∣ m)
  (hc : is_coprime n (2 * a)) : is_square_mod a (m * n) :=
begin
  obtain ⟨u, v, huv⟩ := hs,
  obtain ⟨d, hd⟩ := hd,
  obtain ⟨r, s, hrs⟩ := hc,
  refine ⟨u * (1 + m * s * v), v * (r + d * s * v * (2 - s * u ^ 2)), _⟩,
  linear_combination -m * v * hrs + (-(u ^ 2 * m * s ^ 2 * v ^ 2) + 2 * m * s * v ^ 2) * hd
                       + (2 * m * s * v + 1) * huv,
end

/-- If `a` is a square modulo `m` and `m` is coprime with `2*a`, then `a` is a square
modulo any power of `m`. -/
lemma pow_of_coprime {a m : R} (hs : is_square_mod a m) (hc : is_coprime m (2 * a)) (n : ℕ) :
  is_square_mod a (m ^ n) :=
begin
  induction n with n ih,
  { simp only [pow_zero, is_square_mod_mod_one], },
  { rw [pow_succ, mul_comm],
    cases n with n',
    { simpa only [pow_zero, one_mul] using hs, },
    { exact ih.mul_of_dvd_of_coprime (dvd_pow (dvd_refl m) ne_zero.out) hc, } }
end

end is_square_mod

end general

section integer

/-!
### Squares modulo an integer
-/

namespace is_square_mod

/-- If `a` is a square modulo `m > 0`, then there are `b` and `c` such that
`a - b ^ 2 = m * c` with `0 ≤ b ≤ m/2`. -/
lemma exists_le_half {a m : ℤ} (hm : 0 < m) (h : is_square_mod a m) :
  ∃ b c : ℤ, a - b ^ 2 = m * c ∧ 0 ≤ b ∧ b ≤ m / 2 :=
begin
  obtain ⟨u, v, h⟩ := h,
  rw [← int.mod_add_div' u m] at h,
  cases le_or_lt (u % m) (m / 2) with hu hu,
  { exact ⟨u % m, v + 2 * (u % m) * (u / m) + (u / m) ^ 2 * m,
           by linear_combination h, u.mod_nonneg hm.ne', hu⟩, },
  { refine ⟨m - u % m, v - 2 * (m - u % m) * (1 + u / m) + (1 + u / m) ^ 2 * m,
            by linear_combination h, sub_nonneg.mpr (u.mod_lt_of_pos hm).le, _⟩,
    nth_rewrite 0 ← int.div_add_mod' m 2,
    rw [sub_le_iff_le_add, ← sub_le_iff_le_add',
        (by ring : (m / 2) * 2 + m % 2 - m / 2 = m / 2 + m % 2)],
    replace hu : m / 2 + 1 ≤ u % m := hu,
    have H : m % 2 ≤ 1 := int.lt_add_one_iff.mp (m.mod_lt_of_pos zero_lt_two),
    exact (add_le_add_left H (m / 2)).trans hu, }
end

/-- `a` is a square modulo `m` if and only if it is a square modulo `m.nat_abs`. -/
lemma iff_nat_abs {a m : ℤ} : is_square_mod a m ↔ is_square_mod a m.nat_abs :=
begin
  rcases int.nat_abs_eq m with h | h; nth_rewrite 0 h,
  exact iff_neg,
end

/-- `is_square_mod a m` is equivalent with `is_square (a : zmod m.nat_abs)`. -/
lemma iff_is_square (a m : ℤ) : is_square_mod a m ↔ is_square (a : zmod m.nat_abs) :=
begin
  refine ⟨λ H, _, λ H, _⟩,
  { obtain ⟨b, h⟩ := H,
    refine ⟨(b : zmod m.nat_abs), _⟩,
    rwa [← sq, ← int.cast_pow, ← sub_eq_zero, ← int.cast_sub, zmod.int_coe_zmod_eq_zero_iff_dvd,
         int.coe_nat_abs, abs_dvd], },
  { obtain ⟨b, h⟩ := H,
    refine ⟨b.val_min_abs, _⟩,
    rw [← zmod.coe_val_min_abs b, ← sq, ← int.cast_pow, ← sub_eq_zero, ← int.cast_sub] at h,
    rwa [← abs_dvd, ← int.coe_nat_abs, ← zmod.int_coe_zmod_eq_zero_iff_dvd], }
end

/-- If `m` is a natural number, then `is_square_mod a m` is equivalent with
`is_square (a : zmod m)`. -/
lemma iff_is_square' (a : ℤ) (m : ℕ): is_square_mod a m ↔ is_square (a : zmod m) :=
is_square_mod.iff_is_square a m

/-- `-1` is a square modulo a prime `p` if and only if `p % 4 ≠ 3`. -/
lemma iff_not_three_mod_four (p : ℕ) [fact p.prime] : is_square_mod (-1 : ℤ) p ↔ p % 4 ≠ 3 :=
begin
  rw [is_square_mod.iff_is_square', int.cast_neg, int.cast_one],
  exact zmod.exists_sq_eq_neg_one_iff,
end

/-- If `-1` is a square mod `b` and `0 ≤ b`, then `b` is a sum of two squares. -/
lemma sum_of_squares_of_is_square_mod_neg_one {b : ℤ} (hb : 0 ≤ b) (h : is_square_mod (-1) b) :
  ∃ x y : ℤ, b = x ^ 2 + y ^ 2 :=
begin
  lift b to ℕ using hb,
  replace h : is_square (-1 : zmod b),
  { convert (iff_is_square' _ b).mp h,
    push_cast, },
  obtain ⟨x, y, hxy⟩ := nat.eq_sq_add_sq_of_is_square_mod_neg_one h,
  exact ⟨x, y, by exact_mod_cast hxy⟩,
end

end is_square_mod

end integer
