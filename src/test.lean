import data.list
noncomputable theory
open_locale classical
universe u
variables (α : Type u) (a : α) (l : list α)
theorem count_eq_countp {h : decidable_pred (λ x, a = x)} : l.count a = l.countp (λ x, a = x) := sorry
theorem count_eq_countp' {h : decidable_pred (λ x, a = x)}  : l.count a = l.countp (λ x, x = a) :=
begin
  conv in (_ = a) { rw eq_comm, },
  exact (@count_eq_countp _ a l h), -- error, works with convert
end