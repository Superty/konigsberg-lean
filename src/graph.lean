import data.finset data.multiset
import tactic
import init.classical
noncomputable theory
open_locale classical
local attribute [instance, priority 100000] classical.prop_decidable -- avoid decidability hell

namespace list
def ihead {α : Type} : Π l : list α, l ≠ [] → α
| []       h := absurd rfl h
| (a :: t) h := a
end list

structure multigraph (α : Type) :=
(V : finset α)
(E : multiset (α × α))
(valid_edges : ∀ e : α × α, e ∈ E → e.1 ∈ V ∧ e.2 ∈ V)
(no_self_loops : ∀ {u v}, (u, v) ∈ E → u ≠ v)
namespace multigraph
variable {α : Type}

@[simp]
instance : has_mem (α × α) (multigraph α) := ⟨λ e g, e ∈ g.E⟩

-- @[simp]
-- theorem no_self_loops_mem (g : multigraph α) (v : α) : (v, v) ∉ g :=
-- λ h, h (g.no_self_loops v)

-- def vertex_of_edge {g : multigraph α} {e : α × α} : e ∈ g → e.1 ∈ g.V ∧ e.2 ∈ g.V :=
-- begin
--   intro h,
--   unfold has_mem.mem at h,
--   unfold has_edge at h,
--   exact g.valid_edges h,
-- end

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

def append : Π {s t u : α} (wst : walk g s t) (wtu : walk g t u), walk g s u
| _ _ _ (nil g _) w := w
| _ _ u (cons s v t hmem w1) w2 := cons s v u hmem (append w1 w2)



-- def pop_last : Π {s t : α} (l : walk g s t), (Σ e : g.E, walk g s e.1.1)
-- | _ _ (nil g t) := 
-- | _ _ (cons s _ _ hmem (nil g t)) := ⟨⟨(s, t), hmem⟩, nil g s⟩
-- | _ _ (cons s _ _ hmem (cons t u t hmem2 l)) :=
--     let ⟨x, l⟩ := pop_last (cons t u t hmem2 l) in ⟨x, cons s _ _ hmem l⟩

def length {u v : α} : walk g u v → ℕ := λ w, w.edges.length

-- instance has_coe_to_list : has_coe (walk g : Type) (list (α × α) : Type) := ⟨λ w, w.edges⟩

variables {s t : α}
variable w : walk g s t

lemma valid_edge_of_mem_walk (e : α × α) : e ∈ w.edges → e ∈ g :=
begin
  intro hmem,
  induction w with _ u v w hemem l ih,
  { simp at hmem, exfalso, exact hmem },
  simp at hmem,
  cases hmem with hl hr,
  { rw ← hl at hemem,
    exact hemem, },
  exact ih hr,
end

def count (e : α × α) := finset.fold nat.add 0 (λ u, w.edges.count e) g.V

-- inductive stlist : α → α → Type
-- | single (s : α) : stlist s s
-- | 

@[reducible]
def is_eulerian : Prop :=
∀ u v : α, g.E.countp (λ e, e = (u, v) ∨ e = (v, u)) = w.edges.countp (λ e, e = (u, v) ∨ e = (v, u))
def is_cycle : Prop := s = t
end walk

variable (g : multigraph α)
def sum (f : α → ℕ) : ℕ := multiset.sum (multiset.map f g.V.val)

def degree (v : α) : ℕ := g.E.countp (λ e, ∃ u, e = (u, v) ∨ e = (v, u))

def reachable : α → α → Prop := relation.refl_trans_gen (λ u v, (u, v) ∈ g)
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

theorem countp_cons (p : α → Prop) [∀ a, decidable (p a)] : countp p (a :: l) = ite (p a) 1 0 +  countp p l :=
by {by_cases p a; rw countp; simp [h], ring,}
-- theorem count_eq_countp {h : decidable_pred (λ x, a = x)} {heq : decidable_eq α} : l.count a = l.countp (λ x, a = x) := rfl
-- theorem count_eq_countp' {h : decidable_pred (λ x, a = x)} {h' : decidable_pred (λ x, x = a)}  {heq : decidable_eq α} : l.count a = l.countp (λ x, x = a) :=
-- begin
--   conv in (_ = a) { rw eq_comm, },
--   convert (@count_eq_countp _ a l h _),
-- end

theorem length_filter_eq_sum_map {α : Type} (l : list α) (p : α → Prop) : length (filter p l) = sum (map (λ x, ite (p x) 1 0) l) :=
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

theorem not_mem_of_countp_eq_zero {α : Type} (l : list α) (p : α → Prop) : l.countp p = 0 ↔ ∀ a ∈ l, ¬ p a :=
begin
  split,
  { intros hzero a hmem hp,
    induction l with x l ih,
    { simp at hmem, exact hmem, },
    simp [countp_cons] at *,
    cases hmem with hx hl,
    { rw ← hx at hzero, simp [hp] at hzero, exact hzero, },
    exact ih hzero.left hl,},
  intros h,
  induction l with x l ih,
  { simp, },
  simp [countp_cons],
  split,
  { rw ih,
    intros a hmem,
    exact h a (by simp [hmem]), },
  simp [h x],
end

theorem countp_split {α : Type} (l : list α) (p : α → Prop) (q : α → Prop) : l.countp p = (l.filter q).countp p + (l.filter (λ a, ¬ q a)).countp p :=
begin
  induction l with x l ih,
  { simp, },
  simp [countp_cons],
  by_cases p x,
  { by_cases q x; simp *, },
  simp [h, ih],
end

theorem countp_le_length {α : Type} {l : list α} {p : α → Prop} : l.countp p ≤ l.length :=
begin
  induction l with x l ih,
  simp,
  by_cases p x; simp [h, ih],
  linarith,
end

theorem length_lt_of_filter_of_mem {α : Type} (l : list α) (p : α → Prop) :
    (∃ a ∈ l, ¬ p a) → (l.filter p).length < l.length :=
begin
  intro h,
  cases h with a h,
  cases h with hmem ha,
  induction l with x l ih,
  { simp at ⊢ hmem,
    exfalso,
    exact hmem, },
  rw ← list.countp_eq_length_filter,
  simp [list.countp_cons],
  by_cases heq : a = x,
  { rw ← heq,
    simp [ha],
    have : countp p l ≤ length l, from countp_le_length,
    linarith,
  },
  have : a ∈ l,
  { simp at hmem,
    cases hmem,
    exact absurd hmem heq,
    exact hmem,
  },
  have : l.countp p < length l, by simp [list.countp_eq_length_filter, ih this],
  have hleite : ite (p x) 1 0 ≤ 1, by by_cases p x; simp *,
  linarith,
end

theorem countp_false_eq_zero {l : list α} : l.countp (λ x, false) = 0 :=
by {induction l with x l ih, simp, simp [ih]}

-- theorem countp_ne_zero_of_mem {α : Type} (l : list α) (p : α → Prop) : (∃ a ∈ l, p a) → l.countp ≠ 0

theorem eq_nil_of_no_mem {l : list α} : (∀ a, a ∉ l) → l = [] :=
begin
  intro h,
  induction l with x l ih; simp,
  have : x ∉ (x :: l : list α), from h x,
  simp at this,
  exact this,
end

end list

namespace multiset
theorem card_filter_eq_sum_map {α : Type} (s : multiset α) (p : α → Prop) : card (filter p s) = sum (map (λ x, ite (p x) 1 0) s) :=
by {induction s; simp, exact list.length_filter_eq_sum_map _ _}

-- theorem count_eq_countp (s : multiset α) (a : α): s.count a = s.countp (λ x, a = x) := by {induction s; simp [list.count_eq_countp] }
-- theorem count_eq_countp' (s : multiset α) (a : α): s.count a = s.countp (λ x, x = a) := by {induction s; simp [list.count_eq_countp'] }
theorem countp_false_eq_zero {s : multiset α} : s.countp (λ x, false) = 0 := by {induction s; simp, induction s with x l ih, simp, simp [ih]}

end multiset

-- namespace nat
-- -- we don't seem to have cancellative monoids in mathlib yet
-- variables a b : nat
-- @[simp]
-- lemma add_left_eq_self : a + b = b ↔ a = 0 :=
-- ⟨λ h, @add_right_cancel _ _ a b 0 (by simp [h]), λ h, by simp [h]⟩  

-- @[simp]
-- lemma add_right_eq_self : a + b = a ↔ b = 0 :=
-- ⟨λ h, @add_left_cancel _ _ a b 0 (by simp [h]), λ h, by simp [h]⟩

-- -- @[simp]
-- -- lemma add_self_eq_double : a + a = 2*a :=
-- --   ring,
-- -- end
-- end nat

-- lemma two_dvd_add_self {x : ℤ} : (x + x) % 2 = 0 :=
-- begin
-- end

-- lemma two_dvd_add_self {x : ℕ} : (x + x) % 2 = 0 := by {ring, simp}
-- lemma not_two_dvd_succ_add_self {x : ℕ} : (1 + (x + x)) % 2 = 1 := 
-- begin
--   ring,
--   simp,
--   refl,
-- end

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

-- lemma nonterm_vert_in_walk (x : α) : ∀ (s t : α) (w : walk g s t),
--     s ≠ x → t ≠ x → w.edges.countp (λ e, ∃ u, e = (x, u)) = w.edges.countp (λ e, ∃ u, e = (u, x))
-- | _ _ (walk.nil g s)           := by simp
-- | _ _ (walk.cons s _ _ hmem (walk.nil g v)) := by {intros, simp [list.countp_cons, *]}
-- | _ _  (walk.cons s _ _ hmem (walk.cons v w t hmem2 l)) :=
-- begin
--   intros hnot_start hnot_last,
--   by_cases v = x,
--   { have : w ≠ x,
--     { intro h2,
--       rw [h, h2] at hmem2,
--       exact absurd hmem2 (g.no_self_loops x) },
--     simp [list.countp_cons, *],
--   },
--   have hl := nonterm_vert_in_walk v t (walk.cons v w t hmem2 l),
--   simp [list.countp_cons, *] at ⊢ hl,
--   exact hl,
-- end
-- 

variable {β : Type}

lemma vert_in_walk (x : α) : ∀ (s t : α) (wlk : walk g s t),
    wlk.edges.countp (λ e, ∃ u, e = (x, u)) + ite (t = x) 1 0 =
    wlk.edges.countp (λ e, ∃ u, e = (u, x)) + ite (s = x) 1 0
| _ _ (walk.nil g s)           := by simp
| _ _ (walk.cons s v t hmem w) :=
have hdec : @list.length (α × α) (@walk.edges α g v t w) < 1 + @list.length (α × α) (@walk.edges α g v t w), by linarith,
begin
  have indrw := vert_in_walk v t w,
  by_cases (s = x),
  { have hne : v ≠ x,
    { rw h at hmem,
      have this := g.no_self_loops hmem,
      symmetry,
      exact this,
    },
    simp [list.countp_cons, h, hne] at ⊢ indrw,
    exact indrw,
  },
  by_cases hcase: v = x;
  { simp [list.countp_cons, h, hcase] at ⊢ indrw,
    exact indrw,
  },
end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ psig, psig.2.2.edges.length)⟩], dec_tac := well_founded_tactics.default_dec_tac'}
-- , dec_tac := `[well_founded_tactics.default_dec_tac, suffices : @list.length (α × α) (@walk.edges α g v t w) < 1 + @list.length (α × α) (@walk.edges α g v t w), convert this, exact hwf ] }
--   by { simp [list.countp_cons, *], by_cases (s = x); by_cases (v = x); simp *, }
-- | _ _  (walk.cons s _ _ hmem (walk.cons v w t hmem2 l)) :=
-- begin
--   by_cases (s = x),
--   { set l' := walk.cons v w t hmem2 l,
--     have hne : v ≠ x,
--     { rw h at hmem,
--       have this := g.no_self_loops hmem,
--       symmetry,
--       exact this,
--     },
--     have hl := nonterm_vert_in_walk v t l',
--     simp [hne] at hl,
--     simp [h],
--   }
--   -- by_cases v = x,
--   -- { have : w ≠ x,
--   --   { intro h2,
--   --     rw [h, h2] at hmem2,
--   --     exact absurd hmem2 (g.no_self_loops x) },
--   --   simp [list.countp_cons, *],
--   -- },
--   -- have hl := nonterm_vert_in_walk v t (walk.cons v w t hmem2 l),
--   -- simp [list.countp_cons, *] at ⊢ hl,
--   -- exact hl,
-- end


-- lemma vert_in_walk (x : α) (s : α) (w : walk g s s) :
--     w.edges.countp (λ e, ∃ u, e = (x, u)) = w.edges.countp (λ e, ∃ u, e = (u, x)) := sorry
-- begin
--   by_cases s = x,
--   { cases w with _ _ v _ hmem l,
--     { by simp },
--     have : v ≠ x,
--     { rw h at hmem,
--       have this := g.no_self_loops hmem,
--       symmetry,
--       exact this,
--     },
--     simp [list.countp_cons, *],
--     suffices : ∃ w (e : α × α) (hmem : (e.1, e.2) ∈ g), l = walk.append w (walk.cons e.1 e.2 _ hmem (walk.nil g s)),
--   }
-- end

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

-- variable {β : Type}

-- lemma sum_list (l : list β) (s : multiset α) (r : α → β → Prop) (hins : ∀ (u : α) (v ∈ l), r u v → u ∈ s) (nodup : ∀ (u : α) (v : β) (w : α), r u v → w ≠ u → ¬ r w v) : multiset.sum (s.map (λ u, l.countp (r u))) = l.countp (λ v, ∃ u, r u v) :=
-- begin
--   induction l with x l ih,
--   simp,
--   simp [list.countp_cons],
--   simp [ih (λ u v vmem, hins u v (by simp [vmem]))],
--   rw ← multiset.card_filter_eq_sum_map,
--   rw ← multiset.countp_eq_card_filter,
--   by_cases (∃ u, r u x),
--   { simp [h],
--     cases h with u hu,
--     have : s.countp (λ (a : α), r a x) ≠ 0,
--     { intro h,

--     }
--   }
--   -- induction s with s,
--   -- { simp *,
--   --   cases h with u hu,
--   --   induction s with y s hs,

--   -- }
-- end

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

-- set_option pp.implicit true

@[simp]
lemma exists_and (a : α) (p : α → Prop) : (∃ x, p x) ∧ p a ↔ p a :=
by { split; simp, intro hp, split, exact ⟨a, hp⟩, exact hp, }

lemma injective_count_aux (len : ℕ) {r : α → β → Prop} (nodup : ∀ (x y : α) (b : β),
    x ≠ y → ¬ (r x b ∧ r y b)) : ∀ l1 l2 : list β, l1.length ≤ len → (∀ a : α, l1.countp (r a) = l2.countp (r a)) →
    l1.countp (λ b, ∃ a, r a b) = l2.countp (λ b, ∃ a, r a b) :=
begin
  induction len with len,
  { intros l1 l2 hlen hp,
    simp at hlen,
    have : l1 = list.nil, by rw list.eq_nil_of_length_eq_zero hlen,
    rw this at hp ⊢,
    simp at hp ⊢,
    have : ∀ b ∈ l2, ¬ ∃ a, r a b,
    { intros b hmem h,
      cases h with a ha,
      have : ∀ c ∈ l2, ¬ r a c,
      rw ← list.not_mem_of_countp_eq_zero,
      { symmetry,
        exact hp a, },
      exact absurd ha (this b hmem),
    },
    symmetry,
    rw list.not_mem_of_countp_eq_zero,
    exact this, },
  intros l1 l2 hlen h,
  by_cases hex : ∃ a, ∃ b ∈ l1, r a b,
  { cases hex with a ha,
    rw list.countp_split l1 _ (λ b, r a b),
    rw list.countp_split l2 _ (λ b, r a b),
    repeat {rw @list.countp_filter _ _ _ (λ (b : β), r a b) _ _},
    simp [-list.countp_filter],
    suffices : list.countp (λ (b : β), ∃ (a : α), r a b) (list.filter (λ (a_1 : β), ¬r a a_1) l1) + list.countp (r a) l1 =
    list.countp (λ (b : β), ∃ (a : α), r a b) (list.filter (λ (a_1 : β), ¬r a a_1) l2) + list.countp (r a) l2,
    { convert this }, -- decidability hell
    simp [h a, -list.countp_filter],
    set l1' := (list.filter (λ (a_1 : β), ¬r a a_1) l1),
    set l2' := (list.filter (λ (a_1 : β), ¬r a a_1) l2),

    have hlen' : l1'.length ≤ len,
    { have : l1'.length < l1.length,
      { apply list.length_lt_of_filter_of_mem,
        simp at ⊢ ha,
        exact ha,
      },
      have : nat.succ l1'.length ≤ nat.succ len,
      { apply nat.succ_le_of_lt,
        apply nat.lt_of_lt_of_le this hlen, },
      exact nat.le_of_succ_le_succ this,
    },

    have heqcountp : ∀ l (a' : α) (hne : a' ≠ a), (list.filter (λ (b : β), ¬r a b) l).countp (r a') = l.countp (r a'),
    { intros l a' hne,
      induction l with x l ih,
      simp,
      simp at ih,
      simp [list.countp_cons, ih],
      by_cases r a' x,
      { have : ¬ r a x, { have not_and := nodup a' a x hne, finish [nodup a' a x hne], },
        simp *, },
      simp *,
    },

    have h' : ∀ (a : α), list.countp (r a) l1' = list.countp (r a) l2',
    { intro a',
      by_cases hcase : a' = a,
      { rw hcase,
        simp,
        suffices : list.countp (λ (a : β), false) l1 = list.countp (λ (a : β), false) l2,
        { convert this, }, -- more decidability hell
        simp [list.countp_false_eq_zero],
      },
      rw heqcountp l1 _ hcase,
      rw heqcountp l2 _ hcase,
      exact h a',
    },
    exact len_ih l1' l2' (by simp [hlen']) h', },
  have : ∀ b ∈ l1, ¬ ∃ a, r a b,
  { intros b hmem h,
    cases h with a ha,
    have : ∃ (a : α) (b : β) (H : b ∈ l1), r a b,
    exact ⟨a, ⟨b, ⟨hmem, ha⟩⟩⟩,
    exact absurd this hex, },
  rw list.countp_eq_length_filter,
  rw list.countp_eq_length_filter,
  have : ∀ b, b ∉ list.filter (λ (b : β), ∃ (a : α), r a b) l1,
  { intros b h,
    simp at h,
    exact absurd h.right (this b h.left), },
  rw list.eq_nil_iff_forall_not_mem.mpr this,
  have : ∀ b, b ∉ list.filter (λ (b : β), ∃ (a : α), r a b) l2,
  { intros b h,
    simp at h,
    cases h with hmem hr,
    cases hr with a hr,
    have : list.countp (r a) l2 = 0,
    { rw ← h a,
      have : ∀ b, b ∉ list.filter (r a) l1,
      { intros b h,
        simp at h,
        cases h with hmem hr,
        have : ∃ (a : α) (b : β) (H : b ∈ l1), r a b,
        exact ⟨a, ⟨b, ⟨hmem, hr⟩⟩⟩,
        exact absurd this hex, },
      rw list.countp_eq_length_filter,
      rw list.eq_nil_iff_forall_not_mem.mpr this,
      simp, },
    rw list.countp_eq_length_filter at this,
    have : l2.filter (r a) = [], from list.eq_nil_of_length_eq_zero this,
    have hfilter_mem : b ∈ l2.filter (r a),
    { rw list.mem_filter,
      exact ⟨hmem, hr⟩, },
    rw list.eq_nil_iff_forall_not_mem at this,
    exact absurd hfilter_mem (this b), },
  rw list.eq_nil_iff_forall_not_mem.mpr this,
end

lemma injective_count {l1 l2 : list β} {r : α → β → Prop} (nodup : ∀ (x y : α) (b : β),
    x ≠ y → ¬ (r x b ∧ r y b)) : (∀ a : α, l1.countp (r a) = l2.countp (r a)) →
    l1.countp (λ b, ∃ a, r a b) = l2.countp (λ b, ∃ a, r a b) :=
begin
  -- let l := l1.map (λ b, if h : ∃ a, r a b then some (classical.some h) else none),
  set len := l1.length,
  exact injective_count_aux len nodup l1 l2 (by simp [len]),
end

lemma count_plus (l : list α) (p q : α → Prop) (nodup : ∀ a ∈ l, ¬ (p a ∧ q a)) : l.countp p + l.countp q = l.countp (λ a, p a ∨ q a) :=
begin
  induction l with a l1 ih,
  { simp },
  simp [list.count_cons', list.countp_cons],
  by_cases p a ∨ q a,
  { cases h,
    { have : ¬ q a, by finish,
      simp *, rw ih,
      intros a hmem, exact nodup a (by simp [hmem]),},
    { have : ¬ p a, by finish,
      simp *, rw ih,
      intros a hmem, exact nodup a (by simp [hmem]),} },
  { have hane : ¬ p a, by finish,
    have hbne : ¬ q a, by finish,
    simp *, rw ih,
    intros a hmem, exact nodup a (by simp [hmem]),}
end

-- set_option pp.implicit true

lemma degree_of_eulerian_walk {s t : α} {w : walk g s t} (he : w.is_eulerian) {v : α} :
g.degree v =  list.countp (λ (a : α × α), ∃ (x : α), a = (x, v)) (walk.edges w) +
              list.countp (λ (a : α × α), ∃ (x : α), a = (v, x)) (walk.edges w) :=
begin
  have : g.degree v = w.edges.countp (λ e, ∃ u, e = (u, v) ∨ e = (v, u)),
  { rw degree,
    have he := (λ u, he u v),
    revert he,
    induction g.E with l;
    intro he; simp at *,
    apply injective_count (by finish) he },
  rw this,
  simp [exists_or_distrib],
  suffices :
  list.countp (λ (e : α × α), (∃ (x : α), e = (x, v)) ∨ ∃ (x : α), e = (v, x)) (walk.edges w) =
    list.countp (λ (a : α × α), ∃ (x : α), a = (x, v)) (walk.edges w) +
      list.countp (λ (a : α × α), ∃ (x : α), a = (v, x)) (walk.edges w),
  { convert this, },
  rw ← count_plus,
  intros e hmem h,
  cases h with hl hr,
  cases hl with xl hl,
  cases hr with xr hr,
  rw hr at hl,
  have hmem := w.valid_edge_of_mem_walk _ hmem,
  rw hr at hmem,
  have hv_ne_xr := g.no_self_loops hmem,
  simp at hl,
  finish,
end

lemma degree_constraint_of_eulerian (h : g.is_eulerian) : (∀ v ∈ g.V, g.degree v % 2 = 0) ∨ ∃ s t, g.degree s % 2 = 1 ∧ g.degree t % 2 = 1 ∧ (∀ v ∈ g.V, s ≠ v → t ≠ v → g.degree v % 2 = 0)  :=
begin
  rw is_eulerian at h,
  cases h with s h,
  cases h with t h,
  cases h with w he,
  by_cases hcase : s = t,
  { left,
    intros v hmem,
    have hcnt := vert_in_walk g v _ _ w,
    simp [hcase] at hcnt,
    rw degree_of_eulerian_walk _ he,
    by_cases htv : t = v; simp [htv] at hcnt; rw hcnt; ring; simp,
  },
  right,
  use s, use t,
  split,
  { have hcnt := vert_in_walk g s _ _ w,
    simp [ne.symm hcase] at hcnt,
    rw degree_of_eulerian_walk _ he,
    simp [hcnt],
    ring, simp, refl,
  },
  split,
  { have hcnt := vert_in_walk g t _ _ w,
    simp [hcase] at hcnt,
    rw degree_of_eulerian_walk _ he,
    simp [eq.symm hcnt],
    ring, simp, refl,
  },
  intros v hmem hnes hnet,
  have hcnt := vert_in_walk g v _ _ w,
  rw degree_of_eulerian_walk _ he,
  simp [hnes, hnet] at hcnt,
  simp [hcnt],
  ring, simp, 
end