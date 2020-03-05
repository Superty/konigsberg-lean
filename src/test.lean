import data.multiset
noncomputable theory
open_locale classical

-- set_option pp.implicit true

example : list.countp (λ (e : ℕ × ℕ), ∃ (u : ℕ), e = (u, 0) ∨ e = (0, u))
      [(0, 1), (0, 1), (1, 2), (1, 2), (0, 3), (1, 3), (2, 3)] = 3 :=
begin
  simp,
end