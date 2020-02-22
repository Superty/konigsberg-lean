import data.finset data.multiset
noncomputable theory
open_locale classical
universe u

section multidigraph
structure multidigraph (α : Type) :=
(V : finset α)
(edges : α → α → ℕ)
(valid_edges : ∀ u v, edges u v ≠ 0 → u ∈ V ∧ v ∈ V)
(irreflexive (v : α) : edges v v = 0)
variable {α : Type}
variable (g : multidigraph α)
def has_edge {α : Type} (g : multidigraph α) (u v : α) : Prop := g.edges u v ≠ 0
instance : has_mem (α × α) (multidigraph α) := ⟨λ ⟨u, v⟩ g, has_edge g u v⟩

def is_walk : list (α × α) → Prop
| []  := true
| [e] := e ∈ g
| (e :: f :: t) := e ∈ g ∧ e.2 = f.1 ∧ is_walk t

def degree (v : α) : ℕ := finset.fold nat.add 0 (g.edges v) g.V
def reachable : α → α → Prop := relation.refl_trans_gen (has_edge g)
def connected : Prop := ∀ u v ∈ g.V, reachable g u v

section walk
structure walk := (edges : list (α × α)) (h : is_walk g edges)
instance has_coe_to_list : has_coe (walk g : Type) (list (α × α) : Type) := ⟨λ w, w.edges⟩
end walk
end multidigraph

section multigraph
structure multigraph (α : Type) extends multidigraph α :=
(symmetric : ∀ u v : α, edges u v = edges v u)

variable {α : Type}
instance has_coe_to_multidigraph : has_coe (multigraph α : Type) (multidigraph α : Type) := ⟨multigraph.to_multidigraph⟩

variable g : multigraph α

end multigraph