import data.finset data.multiset
import tactic.abel
noncomputable theory
open_locale classical

def ihead {α : Type} : Π l : list α, l ≠ [] → α
| []       h := absurd rfl h
| (a :: t) h := a

structure multigraph (α : Type) :=
(V : finset α)
(edges : α → α → ℕ)
(valid_edges : ∀ u v, edges u v ≠ 0 → u ∈ V ∧ v ∈ V)
(no_self_loops (v : α) : edges v v = 0)
(undirected : ∀ u v : α, edges u v = edges v u)
namespace multigraph
variable {α : Type}
def has_edge (g : multigraph α) (u v : α) : Prop := g.edges u v ≠ 0
instance : has_mem (α × α) (multigraph α) := ⟨λ ⟨u, v⟩ g, has_edge g u v⟩

def is_walk (g : multigraph α) : list (α × α) → Prop
| []  := true
| [e] := e ∈ g
| (e :: f :: t) := e ∈ g ∧ e.2 = f.1 ∧ is_walk t

structure walk (g : multigraph α) := (edges : list (α × α)) (hnot_nil : edges ≠ list.nil) (h : is_walk g edges)
namespace walk

variable {g : multigraph α}
instance has_coe_to_list : has_coe (walk g : Type) (list (α × α) : Type) := ⟨λ w, w.edges⟩

variable w : walk g
def count (e : α × α) := finset.fold nat.add 0 (λ u, w.edges.count e) g.V

def is_eulerian : Prop :=
∀ u v : α, g.edges u v = w.edges.count (u, v) + w.edges.count (v, u)

def first : α := (ihead w.edges w.hnot_nil).1
def last : α := (list.last w.edges w.hnot_nil).2
def is_cycle : Prop := first w = last w
end walk

variable (g : multigraph α)
def sum (f : α → ℕ) : ℕ := multiset.sum (multiset.map f g.V.val)

def degree (v : α) : ℕ := g.sum (g.edges v)
def reachable : α → α → Prop := relation.refl_trans_gen (has_edge g)
def is_connected : Prop := ∀ u v ∈ g.V, reachable g u v

def is_eulerian : Prop := ∃ (w : walk g), w.is_cycle ∧ w.is_eulerian
end multigraph

open multigraph

variable {α : Type}
variable (g : multigraph α)
variable (hcon : g.is_connected)

namespace list
universe u
variable (a : α)
variable (l : list α)
theorem countp_eq_count [decidable_eq α] : l.count a = l.countp (λ x, eq a x) :=
by induction l with x l ih; refl
end list

lemma test (u v : α) (l : list (α × α)) : list.count (u, v) l = l.countp (λ x, eq (u, v) x) :=
begin
  exact list.countp_eq_count (u, v) l,
end

lemma two_dvd_add_self {x : ℕ} : 2 ∣ x + x := by {rw [← one_mul x, ← add_mul], simp}

namespace list
@[to_additive]
def prod_map_prod {α β : Type} [comm_group β] (l : list α) (f g : α → β) : prod (map (λ x : α, f x * g x) l) = prod (map f l) * prod (map g l) :=
begin
  induction l with x l ih; simp,
  { simp [mul_comm, mul_left_cancel_iff, mul_assoc],
    rw mul_comm (g x) _,
    rw mul_comm (g x) _,
    rw ← mul_assoc,
    rw mul_right_cancel_iff,
    exact ih, }
end
end list
namespace multiset
@[to_additive]
def prod_map_prod {α β : Type} [comm_group β] (s : multiset α) (f g : α → β) : prod (map (λ x : α, f x * g x) s) = prod (map f s) * prod (map g s) :=
by induction s; simp [list.prod_map_prod]
end multiset

lemma even_degree_of_eulerian (h : g.is_eulerian) : ∀ v : α, 2 ∣ g.degree v :=
begin
  intro v,
  rw is_eulerian at h,
  cases h with w hw,
  cases hw with hc he,
  rw walk.is_eulerian at he,

  have heqsum : list.length (w.edges.filter (λ e, e.1 = v)) = list.length (w.edges.filter (λ e, e.2 = v)) := sorry,
  have : g.degree v = g.sum (λ u, w.edges.count (u, v) + w.edges.count (v, u)) := sorry,
  have hquant : g.sum (λ u, w.edges.count (u, v)) = list.length (w.edges.filter (λ e, e.2 = v)),
  { induction w.edges with x l ih,
    swap,
    { by_cases x.2 = v,
      { conv in (list.count _ _) {
          rw list.count_cons',
        },
        rw list.filter_cons_of_pos,
        simp [multiset.prod_map_add],
      },
    }
    -- simp,
    -- rw multigraph.sum,
    -- rw multiset.map_cons,
    -- induction g.V.va??l with y u jh,

  },
  have testtemp : multiset.card (multiset.bind g.V.val (λ u, multiset.repeat (u, v) (w.edges.count (u, v)))) = list.length (w.edges.filter (λ e, e.1 = v)),
  { rw multiset.card_bind,
    
  },
  have : g.degree v = list.length (w.edges.filter (λ e, e.1 = v)) + list.length (w.edges.filter (λ e, e.2 = v)) := sorry,
  rw this,
  rw heqsum,
  exact two_dvd_add_self,
end

#check list.count_filter