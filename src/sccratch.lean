import number_theory.padics.padic_val

example {p n : ℕ} [fact p.prime] (h : n ≠ 0) : even (padic_val_nat p (n ^ 2)) :=
begin
  rw padic_val_nat.pow 2 h,
  exact even_two_mul _,
  -- leaves goal `fact (nat.prime p)`
  exact ⟨fact.out _⟩,
end

example {p n : ℕ} [hp : fact p.prime] (h : n ≠ 0) : even (padic_val_nat p (n ^ 2)) :=
begin
  rw @padic_val_nat.pow _ _ hp 2 h,
  exact even_two_mul _,
  -- works
end

example {p n : ℕ} [fact p.prime] (h : n ≠ 0) : even (padic_val_nat p (n ^ 2)) :=
begin
  simp_rw padic_val_nat.pow 2 h,
  exact even_two_mul _,
  -- works
end

/-- If `a` and `b` are natural numbers, we can write them as `a = a₁*g` and `b = b₁*g`
with `a₁` and `b₁` coprime, where `g` is the gcd of `a` and `b`. -/
-- `nat.exists_coprime'` requires the gcd of `a` and `b` to be positive.
lemma nat.exists_coprime'' (a b : ℕ) :
  ∃ g a₁ b₁ : ℕ, a₁.coprime b₁ ∧ a = a₁ * g ∧ b = b₁ * g :=
begin
  by_cases h : a = 0 ∧ b = 0,
  { exact ⟨0, 1, 1, nat.coprime_one_left 1, h.1, h.2⟩, },
  { have hg := nat.pos_of_ne_zero (mt nat.gcd_eq_zero_iff.mp h),
    obtain ⟨g, a₁, b₁, h₁, h₂, h₃, h₄⟩ := nat.exists_coprime' hg,
    exact ⟨g, a₁, b₁, h₂, h₃, h₄⟩, }
end



lemma part_enat.even_coe_nat (n : ℕ) : even (n : part_enat) ↔ even n :=
begin
  simp [even],
  split; intro h,
  { obtain ⟨r, h⟩ := h,
    obtain ⟨s, hs⟩ : ∃ s : ℕ, r = s,
    { by_cases hd : r.dom,
      { exact ⟨r.get hd, (part_enat.coe_get hd).symm⟩, },
      { have hrr : ¬ (r + r).dom := not_and_of_not_left r.dom hd,
        have hn : (n : part_enat).dom := part_enat.dom_coe n,
        exact false.elim (hrr (h ▸ hn)), } },
    refine ⟨s, _⟩,
    rw hs at h,
    exact_mod_cast h, },
  { obtain ⟨r, h⟩ := h,
    exact ⟨r, by exact_mod_cast h⟩, }
end

