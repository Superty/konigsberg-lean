import data.finset data.multiset
noncomputable theory
open_locale classical

def indicator (p : Prop) [decidable p] : ℕ := if p then 1 else 0

universe u
structure digraph (α : Type) [decidable_eq α] :=
(V : finset α)
(edge : α → α → Prop)
(valid_edges : ∀ u v, edge u v → u ∈ V ∧ v ∈ V)
(irreflexive (v : α) : ¬ edge v v)

variable {α : Type}
instance : has_mem (α × α) (digraph α) := ⟨λ ⟨u, v⟩ g, g.edge u v⟩

structure graph {α : Type} extends digraph α :=
(symmetric : ∀ u v, edge u v → edge v u)

namespace digraph

def is_walk (g : digraph α) : list α → Prop
| []  := true
| [u] := u ∈ g.V
| (u :: v :: t) := (u, v) ∈ g ∧ is_walk (v :: t)

structure walk (g : digraph α)
(seq : list α) (h : is_walk g seq)

namespace walk
-- variable {g : digraph α}
-- def to_list : Π {s t : α}, walk g s t → list α
-- | _ _ (walk.vert v _) :=  [v]
-- | s t (@walk.cons _ g a b c h w) := a :: (to_list w)

-- instance (s t : α) : has_lift (@walk α g s t : Type) (list α : Type) := ⟨to_list⟩

-- def count_vertex (x : α) [decidable_eq α] : Π {s t : α}, walk g s t → Prop
-- | _ _ (walk.vert v _) := true
-- | s t (@walk.cons _ g a b c h w) := x = c ∨ count_vertex w

-- def edge_mem_of_walk (e : α × α) : Π {s t : α}, walk g s t → Prop
-- | _ _ (walk.vert v _) := false
-- | s t (@walk.cons _ g a b c h w) := e = (a, b) ∨ edge_mem_of_walk w

-- instance inst_vertex_mem_of_digraph : has_mem α (digraph α) :=
-- ⟨λ v w, vertex_mem_of_walk v w ⟩
-- instance inst_edge_mem_of_digraph : has_mem (α × α) (digraph α) := edge_mem_of_walk

-- end walk
-- -- theorem walk_valid {s t : α} (w : walk g s t) : ∀ v ∈ w,
-- end digraph
-- []