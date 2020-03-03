import data.real.basic data.set

namespace probability
universe u
variable Ω : Type u
variable P : (Ω → Prop) → ℝ
axiom nonneg : ∀ E : Ω → Prop, P E ≥ 0
axiom unitary : P (λ a, true) = 1
end probability