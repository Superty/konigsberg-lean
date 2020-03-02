import data.finset data.multiset
import tactic.ring tactic.linarith
noncomputable theory
open_locale classical

namespace list
def ihead {α : Type} : Π l : list α, l ≠ [] → α
| []       h := absurd rfl h
| (a :: t) h := a
end list

structure multigraph (α : Type) :=
(V : finset α)
(edges : α → α → ℕ)
(valid_edges : ∀ {u v}, edges u v ≠ 0 → u ∈ V ∧ v ∈ V)
(no_self_loops (v : α) : edges v v = 0)
(undirected : ∀ u v : α, edges u v = edges v u)
namespace multigraph
variable {α : Type}
variable {hinhabited : inhabited α}

@[simp]
instance : has_mem (α × α) (multigraph α) := ⟨λ e g, e ∈ g.E⟩

@[simp]
theorem no_self_loops_mem (g : multigraph α) (v : α) : (v, v) ∉ g :=
λ h, h (g.no_self_loops v)

def vertex_of_edge {g : multigraph α} {e : α × α} : e ∈ g → e.1 ∈ g.V ∧ e.2 ∈ g.V :=
begin
  intro h,
  unfold has_mem.mem at h,
  unfold has_edge at h,
  exact g.valid_edges h,
end

def walk_vertices_match (g : multigraph α) : list (α × α) → Prop
| []  := true
| [e] := true
| (e :: f :: t) := e.2 = f.1 ∧ walk_vertices_match t

def is_walk (g : multigraph α) (l : list (α × α)): Prop :=
(∀{e}, e ∈ l → e ∈ g) ∧  walk_vertices_match g l

inductive walk (g : multigraph α) : α → α → Type
| nil : Π (v : α), walk v v
| cons : Π (u v w : α) (hmem : (u, v) ∈ g) (l : walk v w), walk u w

namespace walk
variables {g : multigraph α}

@[simp]
def edges : Π {s t : α} (w : walk g s t), list (α × α)
| _ _ (nil g t) := []
| _ _ (cons s t w hmem l) := (s, t) :: (@edges t w l)

-- def pop_last : Π {s t : α} (l : walk g s t), (Σ e : g.E, walk g s e.1.1)
-- | _ _ (nil g t) := 
-- | _ _ (cons s _ _ hmem (nil g t)) := ⟨⟨(s, t), hmem⟩, nil g s⟩
-- | _ _ (cons s _ _ hmem (cons t u t hmem2 l)) :=
--     let ⟨x, l⟩ := pop_last (cons t u t hmem2 l) in ⟨x, cons s _ _ hmem l⟩

@[reducible]
instance : has_sizeof (walk g u v) := ⟨λ w, w.edges.length⟩

instance has_coe_to_list : has_coe (walk g : Type) (list (α × α) : Type) := ⟨λ w, w.edges⟩

variables {s t : α}
variable w : walk g s t
def count (e : α × α) := finset.fold nat.add 0 (λ u, w.edges.count e) g.V

-- inductive stlist : α → α → Type
-- | single (s : α) : stlist s s
-- | 

@[reducible]
def is_eulerian : Prop :=
∀ u v : α, g.edges u v = w.edges.count (u, v) + w.edges.count (v, u)
def is_cycle : Prop := s = t
end walk

variable (g : multigraph α)
def sum (f : α → ℕ) : ℕ := multiset.sum (multiset.map f g.V.val)

def degree (v : α) : ℕ := g.sum (g.edges v)

theorem degree_eq_zero_of_non_vertex {v : α} (h : v ∉ g.V) : g.degree v = 0 :=
begin
  rw degree,
  have : ∀ u, g.edges v u = 0,
  { intro u,
    by_contradiction,
    have : v ∈ g.V,
    { have : v ∈ g.V ∧ u ∈ g.V, from g.valid_edges a,
      cases this,
      assumption, },
    exact h this,
  },
  have : g.edges v = λ u, 0,
  { apply funext,
    assumption,
  },
  rw this,
  exact multiset.sum_map_zero,
end

def reachable : α → α → Prop := relation.refl_trans_gen (has_edge g)
@[reducible]
def is_connected : Prop := ∀ u v ∈ g.V, reachable g u v

@[reducible]
def is_eulerian : Prop := ∃ (s t : α) (w : walk g s t), w.is_eulerian
end multigraph

open multigraph

variable {α : Type}
variable (g : multigraph α)
variable (hcon : g.is_connected)


@[simp]
lemma fun_abstract {α β : Type} (f : α → β) : f = (λ x : α, f x) := rfl

-- variable {hdec1 : decidable_pred (λ x : α, a = x)}
-- variable {hdec2 : decidable_pred (λ x : α, x = a)}
-- variable {hdec3 : decidable_eq α}

namespace list
universe u
variable (a : α)
variable (l : list α)

theorem countp_cons {p : α → Prop} : countp p (a :: l) = ite (p a) 1 0 +  countp p l :=
by {by_cases p a; rw countp; simp [h], ring,}
-- theorem count_eq_countp {h : decidable_pred (λ x, a = x)} {heq : decidable_eq α} : l.count a = l.countp (λ x, a = x) := rfl
-- theorem count_eq_countp' {h : decidable_pred (λ x, a = x)} {h' : decidable_pred (λ x, x = a)}  {heq : decidable_eq α} : l.count a = l.countp (λ x, x = a) :=
-- begin
--   conv in (_ = a) { rw eq_comm, },
--   convert (@count_eq_countp _ a l h _),
-- end

theorem length_filter_eq_sum_map {α : Type} (l : list α) (p : α → Prop) [decidable_pred p] : length (filter p l) = sum (map (λ x, ite (p x) 1 0) l) :=
begin
  induction l with x l ih; simp,
  by_cases hx : p x,
  all_goals {
    rw filter_cons_of_pos _ hx <|> rw filter_cons_of_neg _ hx,
    simp [length_cons, ih, hx],},
end

theorem mem_of_mem_sublist {α : Type} {l1 l2 : list α} {a : α} (hsub : l1 <+ l2) (hmem : a ∈ l1) : a ∈ l2 :=
begin
induction hsub,
{ assumption, },
{ simp, right, exact hsub_ih hmem, },
{ simp at hmem, cases hmem,
  { simp [hmem], },
  { simp, right, exact hsub_ih hmem, }}
end
theorem mem_of_mem_suffix {α : Type} {l1 l2 : list α} {a : α} (hsuff : l1 <:+ l2) (hmem : a ∈ l1) : a ∈ l2 := mem_of_mem_sublist (sublist_of_suffix hsuff) hmem
theorem mem_of_mem_prefix {α : Type} {l1 l2 : list α} {a : α} (hpref : l1 <+: l2) (hmem : a ∈ l1) : a ∈ l2 := mem_of_mem_sublist (sublist_of_prefix hpref) hmem
theorem mem_of_mem_infix {α : Type} {l1 l2 : list α} {a : α} (hinf : l1 <:+: l2) (hmem : a ∈ l1) : a ∈ l2 := mem_of_mem_sublist (sublist_of_infix hinf) hmem

theorem cons_suffix {α : Type} {h : α} {t l : list α}  (hsuff : (h :: t) <:+ l) : t <:+ l :=
begin
cases hsuff with pref hsuff,
existsi pref ++ [h],
simp [hsuff],
end

end list

namespace multiset
theorem card_filter_eq_sum_map {α : Type} (s : multiset α) (p : α → Prop) [decidable_pred p] : card (filter p s) = sum (map (λ x, ite (p x) 1 0) s) :=
by {induction s; simp, exact list.length_filter_eq_sum_map _ _}

theorem count_eq_countp (s : multiset α) (a : α): s.count a = s.countp (λ x, a = x) := by {induction s; simp [list.count_eq_countp] }
theorem count_eq_countp' (s : multiset α) (a : α): s.count a = s.countp (λ x, x = a) := by {induction s; simp [list.count_eq_countp'] }
theorem countp_false_eq_zero {s : multiset α} : s.countp (λ x, false) = 0 := by {induction s; simp, induction s with x l ih, simp, simp [ih]}

end multiset

namespace nat
-- we don't seem to have cancellative monoids in mathlib yet
variables a b : nat
@[simp]
lemma add_left_eq_self : a + b = b ↔ a = 0 :=
⟨λ h, @add_right_cancel _ _ a b 0 (by simp [h]), λ h, by simp [h]⟩  

@[simp]
lemma add_right_eq_self : a + b = a ↔ b = 0 :=
⟨λ h, @add_left_cancel _ _ a b 0 (by simp [h]), λ h, by simp [h]⟩
end nat

lemma two_dvd_add_self {x : ℕ} : 2 ∣ x + x := by {rw [← one_mul x, ← add_mul], simp}

def foo : α → α →  list α → α
| _ y []       := y
| x _ (h :: t) := foo h x t

-- example (l : list α) (p : α → Prop) (h : ∀ x ∈ l, p x) : l.filter p = l.length :=
-- begin
--   induction h : l,
--   refl,
--   rw list.countp_cons,
--   rw ih,
-- end

-- def foo (s : multiset α) : Π x ∈ s, Prop := sorry
-- #check foo

-- set_option pp.implicit true

open multigraph

lemma nonterm_vert_in_walk (x : α) : ∀ (s t : α) (w : walk g s t),
    s ≠ x → t ≠ x → w.edges.countp (λ e, e.1 = x) = w.edges.countp (λ e, e.2 = x)
| _ _ (walk.nil g s)           := by simp
| _ _ (walk.cons s _ _ hmem (walk.nil g v)) := by {intros, simp [list.countp_cons, *]}
| _ _  (walk.cons s _ _ hmem (walk.cons v w t hmem2 l)) :=
begin
  intros hnot_start hnot_last,
  by_cases v = x,
  { have : w ≠ x,
    { intro h2,
      rw [h, h2] at hmem2,
      exact absurd hmem2 (g.no_self_loops_mem x) },
    simp [list.countp_cons, *],
  },
  have hl := nonterm_vert_in_walk v t (walk.cons v w t hmem2 l),
  simp [list.countp_cons, *] at ⊢ hl,
  exact hl,
end


lemma vert_in_walk (x : α) (s : α) (w : walk g s s) :
    w.edges.countp (λ e, e.1 = x) = w.edges.countp (λ e, e.2 = x) :=
begin
  by_cases s = x,
  { cases w with _ _ v _ hmem l,
    { by simp },


  }
end

-- lemma bar : ∀ (s t : α) (w : walk g s t), ℕ
-- | _ _  (walk.nil g s)          := 0
-- | _ _ (walk.cons s _ _ hmem l) :=
-- -- have sizeof l < sizeof (walk.cons s v t hmem l), from sorry,
--   match l with
--   | (walk.nil g _) :=
--   | (walk.cons s v t hmem l) :=

-- theorem quant_countp (l : list α) (p : α → Prop) : g.sum 

-- g.sum (λ u, l.countp ) = 

-- list.countp (λ (v : α), ∃ (u : α), u ∈ s ∧ r u v) (x :: l)
-- list.countp (λ (v : α), ∃ (u : α), u ∈ s ∧ r u v) (x :: l)

-- set_option pp.implicit true

variable β : Type

lemma sum_list (l : list β) (s : multiset α) (r : α → β → Prop) (hins : ∀ (u : α) (v ∈ l), r u v → u ∈ s) (nodup : ∀ (u : α) (v : β) (w : α), r u v → w ≠ u → ¬ r w v) : multiset.sum (s.map (λ u, l.countp (r u))) = l.countp (λ v, ∃ u, r u v) :=
begin
  induction l with x l ih,
  simp,
  simp [list.countp_cons],
  simp [ih (λ u v vmem, hins u v (by simp [vmem]))],
  rw ← multiset.card_filter_eq_sum_map,
  rw ← multiset.countp_eq_card_filter,
  by_cases (∃ u, r u x),
  { simp [h],
    cases h with u hu,
    have : s.countp (λ (a : α), r a x) ≠ 0,
    { intro h,

    }
  }
  -- induction s with s,
  -- { simp *,
  --   cases h with u hu,
  --   induction s with y s hs,

  -- }
end

-- lemma sum_list (l : list α) (s : multiset α) (f : α → α) (hinj : function.injective f) : multiset.sum (s.map (λ u, l.count (f u))) = l.countp (λ v, ∃ u, v = f u) :=
-- begin
--   induction l with x l ih,
--   simp,
--   simp [list.countp_cons, ih],
--   rw list.countp_cons,
--   -- rw @list.countp_cons α x l (λ (v : α), ∃ (u : α), u ∈ s ∧ r u v),

--   by_cases (∃ u, r u x),
--   -- simp *,
--   -- induction s with s,
--   -- { simp *,
--   --   cases h with u hu,
--   --   induction s with y s hs,

--   -- }
-- end

lemma even_degree_of_eulerian (h : g.is_eulerian) : ∀ v : α, 2 ∣ g.degree v :=
begin
  intro v,
  by_cases hv : v ∈ g.V,
  swap,
  { simp [g.degree_eq_zero_of_non_vertex hv], },
  rw is_eulerian at h,
  cases h with s h,
  cases h with t h,
  cases h with w he,
  rw walk.is_eulerian at he,

  have heqsum : list.length (w.edges.filter (λ e, e.1 = v)) = list.length (w.edges.filter (λ e, e.2 = v)) := sorry,

  have : g.degree v = g.sum (λ u, w.edges.count (u, v) + w.edges.count (v, u)),
  { rw [degree, multigraph.sum, multigraph.sum],
    induction g.V.val with l; simp,
    induction l with x ih l; simp *, },

  have hquant : Π (l : list (α × α)), l <:+ w.edges → g.sum (λ u, l.count (u, v)) = list.length (l.filter (λ e, e.2 = v)),
  { intros l hsuff,
    induction l with x l ih,
    { simp [list.count_nil, multigraph.sum], },
    have : x ∈ w.edges, from list.mem_of_mem_suffix hsuff (by simp),
    -- have hx : x ∈ g, from w.h.left this,
    { conv in (list.count _ _) { rw list.count_cons' },
      rw multigraph.sum,
      rw multiset.sum_map_add,
      rw ← multigraph.sum,
      rw ← multiset.card_filter_eq_sum_map,
      rw ← multiset.countp_eq_card_filter,
      rw ih (list.cons_suffix hsuff),

      unfold list.filter,
      by_cases x.2 = v; conv in (_ = x) {simp [prod.eq_iff_fst_eq_snd_eq, h],}; simp [h],
      { -- x.2 = v
        rw add_comm,
        rw add_right_cancel_iff,
        suffices : @multiset.countp α (λ (x_1 : α), x_1 = @prod.fst α α x)
    (λ (a : α), classical.prop_decidable ((λ (x_1 : α), x_1 = @prod.fst α α x) a))
    (@finset.val α (@V α g)) = 1, by convert this,
        rw ← @multiset.count_eq_countp' _ g.V.val x.fst,
        rw multiset.count_eq_one_of_mem g.V.nodup,
        exact and.left (vertex_of_edge hx), },
      { -- x.2 ≠ v
        have h : (v = x.snd) = false, by {rw eq_comm at h, simp [eq_comm, eq_false_intro h]},
        conv in (_ ∧ _ = x.2) { rw and_eq_of_eq_false_right h,},
        convert multiset.countp_false_eq_zero }}},
  have : g.degree v = list.length (w.edges.filter (λ e, e.1 = v)) + list.length (w.edges.filter (λ e, e.2 = v)) := sorry,

  rw this,
  rw heqsum,
  exact two_dvd_add_self,
end