import is_square_mod

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

namespace legendre


/-!
### Solubility predicate, assumptions on the coefficients and Legendre's conditions
-/

-- TODO: This can be done in principle for any ring in place of `ℤ`.

/-- We say that a triple of integers `a`, `b`, `c` is *soluble* if the equation
`a*x^2 + b*y^2 + c*z^2 = 0` has a nontrivial solution in integers. -/
def is_soluble (a b c : ℤ) : Prop :=
∃ x y z, a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0 ∧ (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0)

/-- Solubility is preserved when the first two coefficients are swapped. -/
lemma is_soluble.swap₁₂ {a b c : ℤ} (h : is_soluble a b c) : is_soluble b a c :=
begin
  obtain ⟨x, y, z, h, hnt⟩ := h,
  exact ⟨y, x, z, by {rw ← h, ring}, by tauto⟩,
end

/-- Solubility is preserved when the first and the last coefficient are swapped. -/
lemma is_soluble.swap₁₃ {a b c : ℤ} (h : is_soluble a b c) : is_soluble c b a :=
begin
  obtain ⟨x, y, z, h, hnt⟩ := h,
  exact ⟨z, y, x, by {rw ← h, ring}, by tauto⟩,
end

/-- Solubility is preserved when the coefficients are rotated. -/
lemma is_soluble.rotate {a b c : ℤ} (h : is_soluble a b c) : is_soluble b c a :=
begin
  obtain ⟨x, y, z, h, hnt⟩ := h,
  exact ⟨y, z, x, by {rw ← h, ring}, by tauto⟩,
end

/-- Solubility is preserved when the coefficients are multiplied by the same nonzero integer. -/
lemma is_soluble.iff_scale {a b c d : ℤ} (hd : d ≠ 0) :
  is_soluble a b c ↔ is_soluble (d * a) (d * b) (d * c) :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { obtain ⟨x, y, z, h, hnt⟩ := h,
    refine ⟨x, y, z, _, hnt⟩,
    apply_fun ((*) d) at h,
    rw mul_zero at h,
    rw ← h,
    ring, },
  { obtain ⟨x, y, z, h, hnt⟩ := h,
    refine ⟨x, y, z, _, hnt⟩,
    have : d * a * x ^ 2 + d * b * y ^ 2 + d * c * z ^ 2 = d * (a * x ^ 2 + b * y ^ 2 + c * z ^ 2),
    { ring },
    rw [this, mul_eq_zero] at h,
    exact h.resolve_left hd, }
end

/-- Solubility is preserved when the coefficients are negated. -/
lemma is_soluble.neg {a b c : ℤ} (h : is_soluble a b c) : is_soluble (-a) (-b) (-c) :=
begin
  obtain ⟨x, y, z, h, hnt⟩ := h,
  refine ⟨x, y, z, _, hnt⟩,
  simp_rw [neg_mul, ← neg_add, h, neg_zero],
end

lemma is_soluble.mul_iff_mul_mul {a b c d : ℤ} (hd : d ≠ 0) :
  is_soluble (a * d) (b * d) c ↔ is_soluble a b (c * d) :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { obtain ⟨x, y, z, h, h₀⟩ := h,
    refine ⟨d * x, d * y, z, _, _⟩,
    { apply_fun ((*) d) at h,
      rw mul_zero at h,
      rw ← h,
      ring, },
    { rcases h₀ with h₀ | h₀ | h₀,
      { exact or.inl (mul_ne_zero hd h₀), },
      { exact or.inr (or.inl $ mul_ne_zero hd h₀), },
      { exact or.inr (or.inr h₀), } } },
  { obtain ⟨x, y, z, h, h₀⟩ := h,
    refine ⟨x, y, d * z, _, _⟩,
    { apply_fun ((*) d) at h,
      rw mul_zero at h,
      rw ← h,
      ring, },
    { rcases h₀ with h₀ | h₀ | h₀,
      { exact or.inl h₀, },
      { exact or.inr (or.inl h₀), },
      { exact or.inr (or.inr $ mul_ne_zero hd h₀), } } }
end

lemma is_soluble.iff_mul_sq {a b c d : ℤ} (hd : d ≠ 0) :
  is_soluble a b (c * d ^ 2) ↔ is_soluble a b c :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { obtain ⟨x, y, z, h, h₀⟩ := h,
    refine ⟨x, y, d * z, by {rw ← h, ring}, _⟩,
    { rcases h₀ with h₀ | h₀ | h₀,
      { exact or.inl h₀, },
      { exact or.inr (or.inl h₀), },
      { exact or.inr (or.inr $ mul_ne_zero hd h₀), } } },
  { obtain ⟨x, y, z, h, h₀⟩ := h,
    refine ⟨d * x, d * y, z, _, _⟩,
    { apply_fun ((*) (d ^ 2)) at h,
      rw mul_zero at h,
      rw ← h,
      ring, },
    { rcases h₀ with h₀ | h₀ | h₀,
      { exact or.inl (mul_ne_zero hd h₀), },
      { exact or.inr (or.inl $ mul_ne_zero hd h₀), },
      { exact or.inr (or.inr h₀), } } }
end

/-- If a triple is soluble, then there is a solution in coprime integers. -/
lemma is_soluble.primitive {a b c : ℤ} (h : is_soluble a b c) :
  ∃ x y z, a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0 ∧ x.gcd (y.gcd z) = 1 :=
begin
  obtain ⟨x, y, z, h, hnt⟩ := h,
  obtain ⟨g, x₁, y₁, z₁, hg, hgx, hgy, hgz, hg'⟩ := int.make_primitive_3 x y z,
  refine ⟨x₁, y₁, z₁, _, hg'⟩,
  rw [hgx, hgy, hgz] at h,
  have hg₀ : 0 < g,
  { rwa [hg, nat.cast_pos, int.gcd_pos_iff, nat.cast_ne_zero, ← zero_lt_iff, int.gcd_pos_iff], },
  apply_fun ((*) (g ^ 2)) using mul_right_injective₀ (pow_ne_zero 2 hg₀.ne'),
  rw [mul_zero, ← h],
  ring,
end

/-- This is the assumption on the coefficients in Legendre's Theorem:
they are coprime in pairs and squarefree. -/
def coeff_ass (a b c : ℤ) : Prop :=
is_coprime a b ∧ is_coprime b c ∧ is_coprime c a ∧ squarefree a ∧ squarefree b ∧ squarefree c

/-- The assumptions are preserved when the first two coefficients are swapped. -/
lemma coeff_ass.swap₁₂ {a b c : ℤ} (h : coeff_ass a b c) : coeff_ass b a c :=
begin
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := h,
  exact ⟨h₁.symm, h₃.symm, h₂.symm, h₅, h₄, h₆⟩,
end

/-- The assumptions are preserved when the first and the last coefficient are swapped. -/
lemma coeff_ass.swap₁₃ {a b c : ℤ} (h : coeff_ass a b c) : coeff_ass c b a :=
begin
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := h,
  exact ⟨h₂.symm, h₁.symm, h₃.symm, h₆, h₅, h₄⟩,
end

/-- The assumptions are preserved when the coefficients are rotated. -/
lemma coeff_ass.rotate {a b c : ℤ} (h : coeff_ass a b c) : coeff_ass b c a :=
begin
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := h,
  exact ⟨h₂, h₃, h₁, h₅, h₆, h₄⟩,
end

lemma coeff_ass.neg_last {a b c : ℤ} (h : coeff_ass a b c) : coeff_ass a b (-c) :=
begin
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := h,
  exact ⟨h₁, h₂.neg_right, h₃.neg_left, h₄, h₅, h₆.neg⟩,
end

lemma coeff_ass.neg_all {a b c : ℤ} (h : coeff_ass a b c) : coeff_ass (-a) (-b) (-c) :=
begin
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := h,
  exact ⟨h₁.neg_neg, h₂.neg_neg, h₃.neg_neg, h₄.neg, h₅.neg, h₆.neg⟩,
end

lemma is_soluble.primitive'_help₂ {a b c x y z : ℤ} (h : coeff_ass a b c)
  (hs : a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0) (hg : x.gcd (y.gcd z) = 1) :
  is_coprime x y :=
begin
  rw [← int.gcd_eq_one_iff_coprime, nat.eq_one_iff_not_exists_prime_dvd],
  intros p hp,
  by_contra' hf,
  obtain ⟨x₁, rfl⟩ : ↑p ∣ x,
  { rw [← int.coe_nat_dvd] at hf,
    exact hf.trans (int.gcd_dvd_left _ _), },
  obtain ⟨y₁, rfl⟩ : ↑p ∣ y,
  { rw [← int.coe_nat_dvd] at hf,
    exact hf.trans (int.gcd_dvd_right _ _), },
  rw [add_eq_zero_iff_neg_eq, mul_pow, mul_pow, ← mul_assoc, ← mul_assoc, mul_comm a, mul_comm b,
      mul_assoc, mul_assoc, ← mul_add, ← mul_neg, sq, mul_assoc] at hs,
  have hpcz : ↑p ∣ c * z ^ 2 := ⟨_, hs.symm⟩,
  have hpz : ¬ ↑p ∣ z,
  { by_contra' hpz,
    obtain ⟨z₁, rfl⟩ := hpz,
    rw [int.gcd_mul_left, int.nat_abs_of_nat, nat.cast_mul, int.gcd_mul_left, int.nat_abs_of_nat]
      at hg,
    exact hp.not_dvd_one ⟨_, hg.symm⟩, },
  cases int.prime.dvd_mul' hp hpcz with hpc hpz₂,
  { obtain ⟨c₁, rfl⟩ := hpc,
    rw mul_assoc at hs,
    replace hs := (mul_right_inj' (show (↑p : ℤ) ≠ 0, from by exact_mod_cast hp.ne_zero)).mp hs,
    have hpc₁z : ↑p ∣ c₁ * z ^ 2 := ⟨_, hs.symm⟩,
    cases int.prime.dvd_mul' hp hpc₁z with hpc₁ hpz₂',
    { obtain ⟨c₂, rfl⟩ := hpc₁,
      replace h := h.2.2.2.2.2,
      rw [← mul_assoc] at h,
      replace h := h ↑p (dvd_mul_right (↑p * ↑p) c₂),
      exact (prime.not_unit $ nat.prime_iff_prime_int.mp hp) h, },
    { exact hpz (int.prime.dvd_pow' hp hpz₂'), } },
  { exact hpz (int.prime.dvd_pow' hp hpz₂), }
end

lemma is_soluble.primitive'_help₁ {a b c x y z : ℤ} (h : coeff_ass a b c)
  (hs : a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0) (hg : x.gcd (y.gcd z) = 1) :
  is_coprime a y :=
begin
  rw [← int.gcd_eq_one_iff_coprime, nat.eq_one_iff_not_exists_prime_dvd],
  intros p hp,
  by_contra' hf,
  have hyz : is_coprime y z,
  { replace hs : b * y ^ 2 + c * z ^ 2 + a * x ^ 2 = 0 := by { rw ← hs, ring },
    replace hg : y.gcd (z.gcd x) = 1 := by rwa [← int.gcd_assoc, int.gcd_comm],
    exact is_soluble.primitive'_help₂ h.rotate hs hg, },
  obtain ⟨a₁, rfl⟩ : ↑p ∣ a,
  { rw [← int.coe_nat_dvd] at hf,
    exact hf.trans (int.gcd_dvd_left _ _), },
  obtain ⟨y₁, rfl⟩ : ↑p ∣ y,
  { rw [← int.coe_nat_dvd] at hf,
    exact hf.trans (int.gcd_dvd_right _ _), },
  rw [add_eq_zero_iff_neg_eq, mul_pow, ← mul_assoc, mul_comm b, sq ↑p,
      mul_assoc, mul_assoc, mul_assoc, ← mul_add, ← mul_neg] at hs,
  have hpcz : ↑p ∣ c * z ^ 2 := ⟨_, hs.symm⟩,
  cases int.prime.dvd_mul' hp hpcz with hpc hpz₂,
  { obtain ⟨c₁, rfl⟩ := hpc,
    exact int.not_is_coprime_of_mul_prime hp _ _ h.2.2.1, },
  { obtain ⟨z₁, rfl⟩ := int.prime.dvd_pow' hp hpz₂,
    exact int.not_is_coprime_of_mul_prime hp _ _ hyz, }
end

lemma is_soluble.primitive'_help {a b c x y z : ℤ} (h : coeff_ass a b c)
  (hs : a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0) (hg : x.gcd (y.gcd z) = 1) :
  is_coprime (a * x) (b * y) :=
begin
  refine is_coprime.mul_left _ _; refine is_coprime.mul_right _ _,
  { exact h.1, },
  { exact is_soluble.primitive'_help₁ h hs hg, },
  { replace hs : b * y ^ 2 + a * x ^ 2 + c * z ^ 2 = 0 := by { rw ← hs, ring, },
    replace hg : y.gcd (x.gcd z) = 1 := by rwa [int.gcd_comm x, ← int.gcd_assoc, int.gcd_comm _ x],
    exact (is_soluble.primitive'_help₁ h.swap₁₂ hs hg).symm, },
  { exact is_soluble.primitive'_help₂ h hs hg, },
end

/-- If a coefficient triple `(a,b,c)` is soluble and satisfies `coeff_ass`, then there is
a solution `(x,y,z)` such that `a*x`, `b*y` and `c*z` are coprime in pairs. -/
lemma is_soluble.primitive' {a b c : ℤ} (h : is_soluble a b c) (h' : coeff_ass a b c) :
  ∃ x y z, a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0 ∧ is_coprime (a * x) (b * y) ∧
    is_coprime (b * y) (c * z) ∧ is_coprime (c * z) (a * x) :=
begin
  obtain ⟨x, y, z, hs, hg⟩ := h.primitive,
  refine ⟨x, y, z, hs, is_soluble.primitive'_help h' hs hg, _, _⟩,
  { have hs' : b * y ^ 2 + c * z ^ 2 + a * x ^ 2 = 0 := by { rw ← hs, ring, },
    have hg' : y.gcd (z.gcd x) = 1 := by rwa [int.gcd_comm, int.gcd_assoc] at hg,
    exact is_soluble.primitive'_help h'.rotate hs' hg', },
  { have hs' : c * z ^ 2 + a * x ^ 2 + b * y ^ 2 = 0 := by { rw ← hs, ring, },
    have hg' : z.gcd (x.gcd y) = 1 := by rwa [int.gcd_comm, int.gcd_assoc],
    exact is_soluble.primitive'_help h'.rotate.rotate hs' hg', }
end

/-- This is the first solubility conditions in Legendre's Theorem: the coefficients
do not all have the same sign. -/
def condition₁ (a b c : ℤ) : Prop :=
¬ (0 < a ∧ 0 < b ∧ 0 < c) ∧ ¬ (a < 0 ∧ b < 0 ∧ c < 0)

lemma condition₁_iff {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
  condition₁ a b c ↔ (0 < a ∧ 0 < b ∧ c < 0) ∨ (0 < a ∧ b < 0 ∧ 0 < c) ∨ (a < 0 ∧ 0 < b ∧ 0 < c) ∨
                     (a < 0 ∧ b < 0 ∧ 0 < c) ∨ (a < 0 ∧ 0 < b ∧ c < 0) ∨ (0 < a ∧ b < 0 ∧ c < 0) :=
begin
  dsimp only [condition₁],
  cases ha.lt_or_lt with ha₁ ha₁;
    simp only [asymm ha₁, ha₁, false_and, not_false_iff, true_and, not_and, not_lt, false_and,
               not_false_iff, or_false, false_or, and_true];
    cases hb.lt_or_lt with hb₁ hb₁;
      simp only [asymm hb₁, hb₁, is_empty.forall_iff, forall_true_left, false_and, true_and,
                 or_false, false_or, lt_or_lt_iff_ne, ne.def, true_iff, le_iff_eq_or_lt, hc.symm,
                 hc, not_false_iff, or_iff_right_iff_imp],
end

/-- This is the second solubility condition in Legendre's theorem: the negative product
of each pair of coefficients is a square modulo the third. -/
def condition₂ (a b c : ℤ) : Prop :=
is_square_mod (-b * c) a ∧ is_square_mod (-a * c) b ∧ is_square_mod (-a * b) c

lemma condition₂.rotate {a b c : ℤ} (h : condition₂ a b c) : condition₂ b c a :=
begin
  have H : ∀ x y : ℤ, -x * y = -y * x := λ x y, by ring,
  obtain ⟨ha, hb, hc⟩ := h,
  rw H at hb hc,
  exact ⟨hb, hc, ha⟩,
end

lemma condition₂.neg  {a b c : ℤ} (h : condition₂ a b c) : condition₂ (-a) (-b) (-c) :=
begin
  have H : ∀ x y : ℤ, -(-x) * -y = -x * y := λ x y, by ring,
  obtain ⟨ha, hb, hc⟩ := h,
  rw [← is_square_mod.iff_neg, ← H] at ha hb hc,
  exact ⟨ha, hb, hc⟩,
end

/-!
### The conditions are necessary
-/

/-- The first condition in Legendre's Theorem is necessary. -/
lemma necessary₁ {a b c : ℤ} (h : is_soluble a b c) : ¬ (0 < a ∧ 0 < b ∧ 0 < c) :=
begin
  obtain ⟨x, y, z, h, hnt⟩ := h,
  contrapose! hnt,
  have hx := mul_nonneg hnt.1.le (sq_nonneg x),
  have hy := mul_nonneg hnt.2.1.le (sq_nonneg y),
  have hz := mul_nonneg hnt.2.2.le (sq_nonneg z),
  replace hx : a * x ^ 2 = 0 := by linarith,
  replace hy : b * y ^ 2 = 0 := by linarith,
  replace hz : c * z ^ 2 = 0 := by linarith,
  rw [mul_eq_zero, sq_eq_zero_iff] at hx hy hz,
  exact ⟨hx.resolve_left hnt.1.ne', hy.resolve_left hnt.2.1.ne', hz.resolve_left hnt.2.2.ne'⟩,
end

/-- The second condition in Legendre's Theorem is necessary. -/
lemma necessary₂ {a b c : ℤ} (h : is_soluble a b c) (h' : coeff_ass a b c) :
  is_square_mod (-b * c) a :=
begin
  obtain ⟨x, y, z, h, haxby, hbycz, hczax⟩ := is_soluble.primitive' h h',
  rw [add_eq_zero_iff_eq_neg] at h,
  apply_fun ((*) b) at h,
  rw [mul_neg, ← mul_assoc, ← neg_mul, mul_add, ← mul_assoc, ← mul_assoc, mul_comm _ a, mul_assoc,
      ← sq, ← mul_pow, ← eq_sub_iff_add_eq, ← neg_mul] at h,
  have H : is_square_mod (-b * c * z ^ 2) a := ⟨b * y, _, h.symm⟩,
  have hcz : is_coprime a z :=
    is_coprime.of_mul_left_left (is_coprime.of_mul_right_right hczax.symm),
  exact H.of_mul_sq_of_coprime_left hcz,
end

/-- The conditions in Legendre's Theorem are necessary. -/
lemma necessary {a b c : ℤ} (h : is_soluble a b c) (h' : coeff_ass a b c) :
  condition₁ a b c ∧ condition₂ a b c :=
begin
  refine ⟨⟨necessary₁ h, _⟩,
    ⟨necessary₂ h h', necessary₂ h.swap₁₂ h'.swap₁₂, necessary₂ h.rotate.rotate h'.rotate.rotate⟩⟩,
  have := necessary₁ h.neg,
  simpa [neg_pos] using this,
end


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
lemma is_soluble_equal {b : ℤ} (hb : 0 < b) (h : is_square_mod (-1) b) : is_soluble b b (-1) :=
begin
  obtain ⟨r, s, hrs⟩ := h.sum_of_squares_of_is_square_mod_neg_one hb.le,
  exact ⟨r, s, r ^ 2 + s ^ 2, by {rw hrs, ring}, or.inr $ or.inr $ by {rw ← hrs, exact hb.ne'}⟩,
end

/-- This lemma is used to reduce the statement for `a` and `b` to the statement for `A` and `b`
with some `0 < A < a`. -/
lemma descent {a b : ℤ} (hb : 0 < b) (hba : b < a) (h : is_square_mod b a) :
  ∃ A c m : ℤ, c ^ 2 - b = a * (m ^ 2 * A) ∧ squarefree A ∧ 0 < A ∧ A < a :=
begin
  obtain ⟨c, t, h₁, h₂, h₃⟩ := h.exists_le_half (hb.trans hba),
  have ht₀ : t ≤ 0, by nlinarith,
  rcases ht₀.eq_or_lt with rfl | htn,
  { change 1 ≤ b at hb,
    exact ⟨1, c, 0, by linear_combination -h₁, squarefree_one,
           zero_lt_one, hb.trans_lt hba⟩, },
  obtain ⟨A, m, ht, hA⟩ := int.sq_mul_squarefree (-t),
  have hA₀ : 0 < A := pos_of_mul_pos_right (by rwa [ht, neg_pos]) (sq_nonneg m),
  refine ⟨A, c, m, by linear_combination -h₁ - a * ht, hA, hA₀, _⟩,
  replace h₃ : 2 * c ≤ a :=
    ((mul_le_mul_left zero_lt_two).mpr h₃).trans (int.mul_div_le zero_lt_two a),
  have H : a * (4 * m ^ 2 * A) < a * a,
  { calc
      a * (4 * m ^ 2 * A) = (2 * c) ^ 2 - 4 * b : by linear_combination 4 * h₁ + 4 * a * ht
                      ... < (2 * c) ^ 2         : int.sub_lt_self _ (mul_pos zero_lt_four hb)
                      ... ≤ a ^ 2               : sq_le_sq' (by linarith [hb, hba, h₂]) h₃
                      ... = a * a               : sq a, },
  have hm₀ : m ≠ 0,
  { rintro rfl,
    rw [zero_pow zero_lt_two, zero_mul, eq_comm, neg_eq_zero] at ht,
    exact htn.ne ht, },
  calc 
      A = 1 * A         : (one_mul A).symm
    ... ≤ 4 * m ^ 2 * A : mul_le_mul_of_nonneg_right (by {change 0 < 4 * m ^ 2, positivity}) hA₀.le
    ... < a             : lt_of_mul_lt_mul_left H (by linarith),
end

/-- This shows that the first condition, `is_square_mod a b` is preserved when we replace `a`
by `A` (as obtained from `legendre.descent`). -/
lemma condition_i {A a b c m : ℤ} (sa : squarefree a) (sb : squarefree b) (h₁ : is_square_mod a b)
  (h₃ : is_square_mod (-a * b / (a.gcd b) ^ 2) (a.gcd b)) (h' : c ^ 2 - b = a * (m ^ 2 * A)) :
  is_square_mod A b :=
begin
  obtain ⟨g, a₁, b₁, c₁, hg, rfl, rfl, rfl, h⟩ := int.make_primitive_3 a b c,
  have hg₀ : g ≠ 0 := left_ne_zero_of_mul sa.ne_zero,
  have hag := int.is_coprime_of_squarefree_mul sa,
  have hbg := int.is_coprime_of_squarefree_mul sb,
  replace h' : g * (c₁ ^ 2 * g - b₁) = g * (a₁ * (m ^ 2 * A)) := by linear_combination h',
  replace h' := mul_left_cancel₀ hg₀ h',
  have hg₁ : is_coprime a₁ b₁,
  { by_contra hf,
    obtain ⟨p, hp, ⟨a₁, rfl⟩, ⟨b₁, rfl⟩⟩ := int.not_is_coprime_iff_exists_prime_dvd.mp hf,
    have H : ↑p ∣ c₁ ^ 2 * g := ⟨b₁ + a₁ * (m ^ 2 * A), by linear_combination h'⟩,
    obtain ⟨c₁, rfl⟩ := int.prime.dvd_pow' hp (hbg.of_mul_right_left.symm.dvd_of_dvd_mul_right H),
    simp only [int.gcd_mul_left, nat.cast_mul, int.nat_abs_of_nat] at h,
    exact hp.not_dvd_one ⟨_, h.symm⟩, },
  rw [int.gcd_mul_left, int.gcd_eq_one_iff_coprime.mpr hg₁, mul_one, int.nat_abs_sq,
      ← is_square_mod.iff_nat_abs, (by ring : -(g * a₁) * (g * b₁) = (-a₁ * b₁) * g ^ 2),
      int.mul_div_cancel _ (pow_ne_zero 2 hg₀)] at h₃,
  refine is_square_mod.mul_of_coprime _ _ hbg,
  { have H := is_coprime.mul_add_right_right hbg.neg_right (c₁ ^ 2),
    rw [← sub_eq_add_neg, h', sq, ← mul_assoc, mul_comm a₁, mul_assoc, mul_assoc] at H,
    apply_fun ((*) a₁) at h',
    rw [mul_sub, sub_eq_add_neg, ← eq_sub_iff_add_eq, ← mul_assoc, mul_comm _ g, ← neg_mul,
        (by ring : a₁ * (a₁ * (m ^ 2 * A)) = A * (a₁ * m) ^ 2)] at h',
    exact (h₃.of_dvd_sub ⟨_, h'.symm⟩).of_mul_sq_of_coprime_left
            (hag.mul_right H.of_mul_right_left), },
  { have ha := is_coprime.mul_left hbg hg₁,
    have hsm : is_square_mod (g * a₁ * ((m ^ 2) * A)) b₁ :=
      ⟨c₁ * g, -g, by linear_combination -g * h'⟩,
    have hm : is_coprime b₁ m,
    { by_contra hf,
      obtain ⟨p, hp, ⟨b₂, rfl⟩, ⟨m', rfl⟩⟩ := int.not_is_coprime_iff_exists_prime_dvd.mp hf,
      rw sub_eq_iff_eq_add at h',
      have H : ↑p ∣ c₁ ^ 2 * g := ⟨a₁ * p * m' ^ 2 * A + b₂, by {rw h', ring}⟩,
      obtain ⟨c₂, rfl⟩ := int.prime.dvd_pow' hp (hbg.symm.of_mul_left_left.dvd_of_dvd_mul_right H),
      obtain ⟨b₃, rfl⟩ : ↑p ∣ b₂,
      { refine ⟨c₂ ^ 2 * g - a₁ * m' ^ 2 * A, _⟩,
        have : function.injective ((*) (p : ℤ)) :=
          mul_right_injective₀ (nat.cast_ne_zero.mpr hp.ne_zero),
        apply_fun ((*) (p : ℤ)) using this,
        linear_combination -h', },
      exact hp.not_unit (int.of_nat_is_unit.mp $ sb (p : ℤ) ⟨b₃ * g, by ring⟩), },
    exact (hsm.of_mul h₁.of_mul_right ha).of_mul_sq_of_coprime_right hm, }
end

/-- This shows that the third condition, `is_square_mod (-a*b/(a.gcd b)^2) (a.gcd b)`
is preserved when we replace `a` by `A` (as obtained from `legendre.descent`). -/
lemma condition_iii {A a b c m : ℤ} (sb: squarefree b) (h₁ : is_square_mod a b)
  (h' : c ^ 2 - b = a * (m ^ 2 * A)) :
  is_square_mod (-A * b / (A.gcd b) ^ 2) (A.gcd b) :=
begin
  obtain ⟨g, A₁, b₁, c₁, hg, rfl, rfl, rfl, h⟩ := int.make_primitive_3 A b c,
  have hg₀ : g ≠ 0 := left_ne_zero_of_mul sb.ne_zero,
  have hbg := int.is_coprime_of_squarefree_mul sb,
  replace h' : g * (c₁ ^ 2 * g - b₁) = g * (a * (m ^ 2 * A₁)) := by linear_combination h',
  replace h' := mul_left_cancel₀ hg₀ h',
  have hg₁ : is_coprime A₁ b₁, -- maybe prove a lemma; see similar statement above
  { by_contra hf,
    obtain ⟨p, hp, ⟨A₂, rfl⟩, ⟨b₂, rfl⟩⟩ := int.not_is_coprime_iff_exists_prime_dvd.mp hf,
    have H : ↑p ∣ c₁ ^ 2 * g := ⟨b₂ + a * (m ^ 2 * A₂), by linear_combination h'⟩,
    obtain ⟨c₂, rfl⟩ := int.prime.dvd_pow' hp (hbg.of_mul_right_left.symm.dvd_of_dvd_mul_right H),
    simp only [int.gcd_mul_left, nat.cast_mul, int.nat_abs_of_nat] at h,
    exact hp.not_dvd_one ⟨_, h.symm⟩, },
  rw [int.gcd_mul_left, int.gcd_eq_one_iff_coprime.mpr hg₁, mul_one, int.nat_abs_sq,
      ← is_square_mod.iff_nat_abs, (by ring : -(g * A₁) * (g * b₁) = (-A₁ * b₁) * g ^ 2),
      int.mul_div_cancel _ (pow_ne_zero 2 hg₀)],
  obtain ⟨u, v, huv⟩ := h₁.of_mul_left,
  exact ⟨u * m * A₁, A₁ * (v * m ^ 2 * A₁ - c₁ ^ 2),
         by linear_combination A₁ * h' + A₁ ^ 2 * m ^ 2 * huv⟩,
end

/-- If we have a solution for `A` and `b` (with `A` obtained from `legendre.descent`),
then there is also a solution for `a` and `b`. -/
lemma is_soluble_transfer {A a b c m : ℤ} (hm : m ≠ 0) (hA : A ≠ 0) (ha : a ≠ 0)
  (h : is_soluble A b (-1)) (h' : c ^ 2 - b = a * (m ^ 2 * A)) :
  is_soluble a b (-1) :=
begin
  obtain ⟨x, y, z, h, hnt⟩ := h,
  refine ⟨m * A * x, c * y + z, b * y + c * z,
          by linear_combination a * m ^ 2 * A * h + (b * y ^ 2 - z ^ 2) * h', _⟩,
  by_contra' hf,
  obtain ⟨h₁, h₂, h₃⟩ := hf,
  have hy : (c ^ 2 - b) * y = 0 := by linear_combination c * h₂ - h₃,
  have hz : (c ^ 2 - b) * z = 0 := by linear_combination -b * h₂ + c * h₃,
  have hcb : c ^ 2 - b ≠ 0,
  { rw h',
    exact mul_ne_zero ha (mul_ne_zero (pow_ne_zero 2 hm) hA), },
  rcases hnt with hx' | hy' | hz',
  { exact hx' (eq_zero_of_ne_zero_of_mul_left_eq_zero (mul_ne_zero hm hA) h₁), },
  { exact hy' (eq_zero_of_ne_zero_of_mul_left_eq_zero hcb hy), },
  { exact hz' (eq_zero_of_ne_zero_of_mul_left_eq_zero hcb hz), },
end

/-- This shows the variant of Legendre's Theorem under the additional assumption that `b < a`. -/
lemma is_soluble_neg_one_of_lt {a b : ℤ} (sa : squarefree a) (sb : squarefree b) (hb : 0 < b)
  (hba : b < a) (h₁ : is_square_mod a b) (h₂ : is_square_mod b a)
  (h₃ : is_square_mod (-a * b / (a.gcd b) ^ 2) (a.gcd b)) :
  is_soluble a b (-1) :=
begin
  lift b to ℕ using hb.le,
  lift a to ℕ using (hb.trans hba).le,
  induction a using nat.strong_induction_on with a ih generalizing b,
  obtain ⟨A, c, m, h', sf, hA, te⟩ := descent hb hba h₂,
  rcases eq_or_ne m 0 with rfl | hm,
  { exact ⟨0, 1, c, by linear_combination -h', or.inr (or.inl one_ne_zero)⟩, },
  have b1 := condition_i sa sb h₁ h₃ h',
  have b2 : is_square_mod (b : ℤ) A := ⟨c, -a * m ^ 2, by linear_combination -h'⟩,
  have b3 := condition_iii sb h₁ h',
  lift A to ℕ using hA.le,
  refine is_soluble_transfer hm sf.ne_zero sa.ne_zero _ h',
  rcases lt_trichotomy A b with hAb | rfl | hAb,
  { rw [neg_mul, mul_comm, ← neg_mul, int.gcd_comm] at b3,
    exact (ih b (nat.cast_lt.mp hba) sb _ sf hA (nat.cast_lt.mpr hAb) b2 b1 b3).swap₁₂, },
  { simp only [neg_mul, int.gcd_self, int.nat_abs_of_nat, ← sq, int.neg_div_of_dvd,
               int.div_self (sq_pos_of_ne_zero _ hb.ne').ne'] at b3,
    exact is_soluble_equal hb b3, },
  { exact ih A (nat.cast_lt.mp te) sf _ sb hb (nat.cast_lt.mpr hAb) b1 b2 b3, }
end

/-- This is the (interesting direction of) the variant of Legendre's Theorem:
if `a` and `b` are positive and squarefree, `a` is a square modulo `b`, `b` is a square
modulo `a`, and `-a*b/(a.gcd b)^2` is a square modulo `a.gcd b`, then the equation
`a*x^2 + b*y^2 = z^2` has a nontrivial solution in integers. -/
theorem is_soluble_neg_one {a b : ℤ} (ha₀ : 0 < a) (hb₀ : 0 < b) (ha : squarefree a)
  (hb : squarefree b) (hab : is_square_mod a b) (hba : is_square_mod b a)
  (hd : is_square_mod (-a * b / (a.gcd b) ^ 2) (a.gcd b)) :
  is_soluble a b (-1) :=
begin
  rcases lt_trichotomy a b with hab' | rfl | hab',
  { rw [neg_mul, mul_comm, ← neg_mul, int.gcd_comm] at hd,
    exact (is_soluble_neg_one_of_lt hb ha ha₀ hab' hba hab hd).swap₁₂ },
  { rw [neg_mul, int.gcd_self, ← sq, int.nat_abs_sq, int.neg_div_of_dvd ⟨1, (mul_one _).symm⟩,
        int.div_self (sq_pos_of_ne_zero _ hb₀.ne').ne', ← int.eq_nat_abs_of_zero_le ha₀.le] at hd,
    exact is_soluble_equal ha₀ hd, },
  { exact is_soluble_neg_one_of_lt ha hb hb₀ hab' hab hba hd, }
end

/-- This shows the sufficiency of the conditions in Legendre's Theorem when the first two
coefficients are positive and the last is negative. -/
lemma sufficient' {a b c : ℤ} (ha₁ : 0 < a) (hb₁ : 0 < b) (hc₁ : 0 < c) (h₂ : condition₂ a b (-c))
  (h' : coeff_ass a b c) :
  is_soluble a b (-c) :=
begin
  obtain ⟨ha₂, hb₂, hc₂⟩ := h₂,
  obtain ⟨hab, hbc, hca, ha, hb, hc⟩ := h',
  rw neg_mul_neg at ha₂ hb₂,
  rw [is_square_mod.iff_neg, neg_mul] at hc₂,
  rw [(by ring : -c = (-1) * c), ← is_soluble.mul_iff_mul_mul hc₁.ne'],
  refine is_soluble_neg_one (mul_pos ha₁ hc₁) (mul_pos hb₁ hc₁)
    ((int.squarefree_mul hca.symm).mpr ⟨ha, hc⟩) ((int.squarefree_mul hbc).mpr ⟨hb, hc⟩) 
    (hb₂.mul_of_coprime (is_square_mod_mul_self a c) hbc)
    (ha₂.mul_of_coprime (is_square_mod_mul_self b c) hca.symm) _,
  have hg : ((a * c).gcd (b * c) : ℤ) = c :=
  by rw [int.gcd_mul_right, int.gcd_eq_one_iff_coprime.mpr hab, one_mul,
         int.nat_abs_of_nonneg hc₁.le],
  rwa [hg, neg_mul, (by ring : a * c * (b * c) = (a * b) * c ^ 2), ← neg_mul,
       int.mul_div_cancel _ (pow_ne_zero 2 hc₁.ne')],
end

/-- This shows that the conditions in Legendre's Theorem are sufficient. -/
lemma sufficient {a b c : ℤ} (h₁ : condition₁ a b c) (h₂ : condition₂ a b c)
  (h' : coeff_ass a b c) :
  is_soluble a b c :=
begin
  have h'' := h';
  obtain ⟨hab, hbc, hca, ha, hb, hc⟩ := h'', clear hab hbc hca,
  rcases (condition₁_iff ha.ne_zero hb.ne_zero hc.ne_zero).mp h₁ with H | H | H | H | H | H,
  { rw ← neg_neg c at h₂ H ⊢,
    exact sufficient' H.1 H.2.1 (neg_lt_zero.mp H.2.2) h₂ h'.neg_last, },
  { rw ← neg_neg b at h₂ H ⊢,
    exact is_soluble.rotate (sufficient' H.2.2 H.1 (neg_lt_zero.mp H.2.1)
            h₂.rotate.rotate h'.rotate.rotate.neg_last), },
  { rw ← neg_neg a at h₂ H ⊢,
    exact is_soluble.rotate (is_soluble.rotate $ sufficient' H.2.1 H.2.2 (neg_lt_zero.mp H.1)
            h₂.rotate h'.rotate.neg_last), },
  { rw [← neg_neg a, ← neg_neg b] at H ⊢,
    rw ← neg_neg c,
    simp_rw neg_lt_zero at H,
    refine is_soluble.neg (sufficient' H.1 H.2.1 H.2.2 h₂.neg _),
    rw ← neg_neg c,
    exact h'.neg_all.neg_last, },
  { rw [← neg_neg a, ← neg_neg c] at H ⊢,
    rw ← neg_neg b,
    simp_rw neg_lt_zero at H,
    refine is_soluble.neg (is_soluble.rotate $ sufficient' H.2.2 H.1 H.2.1 h₂.rotate.rotate.neg _),
    rw ← neg_neg b,
    exact h'.rotate.rotate.neg_all.neg_last, },
  { rw [← neg_neg b, ← neg_neg c] at H ⊢,
    rw ← neg_neg a,
    simp_rw neg_lt_zero at H,
    refine is_soluble.neg (is_soluble.rotate $ is_soluble.rotate $ sufficient' H.2.1 H.2.2 H.1
      h₂.rotate.neg _),
    rw ← neg_neg a,
    exact h'.rotate.neg_all.neg_last, }
end

/-- The main result: *Legendre's Theorem* on ternary quadratic forms. Let `a`, `b`, `c`
be pairwise coprime and squarefree integers. Then the equation `a*x^2 + b*y^2 + c*z^2 = 0`
has a nontrivial solution in integers if and only if not all of `a`, `b`, `c` have the
same sign and `-a*b` is a square modulo `c`, `-b*c` is a square modulo `a` and 
`-a*c` is a square modulo `b`.
-/
theorem is_soluble_iff {a b c : ℤ} (h : coeff_ass a b c) :
  is_soluble a b c ↔ condition₁ a b c ∧ condition₂ a b c :=
⟨λ H, necessary H h, λ H, sufficient H.1 H.2 h⟩

end legendre
