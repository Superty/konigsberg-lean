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

def walk_vertices_match (g : multigraph α) : list (α × α) → Prop
| []  := true
| [e] := true
| (e :: f :: t) := e.2 = f.1 ∧ walk_vertices_match t

def is_walk (g : multigraph α) (l : list (α × α)): Prop :=
(∀{e}, e ∈ l → e ∈ g) ∧  walk_vertices_match g l

inductive walk (g : multigraph α) : α → α → Type
| nil : Π (v ∈ g.V), walk v v
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

def s_mem : Π {s t : α} (w : walk g s t), s ∈ g.V
| _ _ (nil g t) := t
| _ _ (cons s v t hmem l) := (g.valid_edges _ hmem).left

def t_mem : Π {s t : α} (w : walk g s t), t ∈ g.V
| _ _ (nil g t) := t
| _ _ (cons s v t hmem l) := t_mem l

def length {u v : α} : walk g u v → ℕ := λ w, w.edges.length

variables {s t : α}
variable w : walk g s t

lemma valid_edge_of_mem_walk (e : α × α) : e ∈ w.edges → e ∈ g :=
begin
  intro hmem,
  induction w with _ _ u v w hemem l ih,
  { simp at hmem, exfalso, exact hmem },
  simp at hmem,
  cases hmem with hl hr,
  { rw ← hl at hemem,
    exact hemem, },
  exact ih hr,
end

@[reducible]
def is_eulerian : Prop :=
∀ u v : α, g.E.countp (λ e, e = (u, v) ∨ e = (v, u)) = w.edges.countp (λ e, e = (u, v) ∨ e = (v, u))
def is_cycle : Prop := s = t
end walk

variable (g : multigraph α)
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

namespace list
universe u
variable (a : α)
variable (l : list α)

theorem countp_cons (p : α → Prop) [∀ a, decidable (p a)] :
    countp p (a :: l) = ite (p a) 1 0 +  countp p l :=
    by {by_cases p a; rw countp; simp [h], ring,}

theorem length_filter_eq_sum_map {α : Type} (l : list α) (p : α → Prop) : length (filter p l) = sum (map (λ x, ite (p x) 1 0) l) :=
begin
  induction l with x l ih; simp,
  by_cases hx : p x,
  all_goals {
    rw filter_cons_of_pos _ hx <|> rw filter_cons_of_neg _ hx,
    simp [length_cons, ih, hx],},
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

theorem countp_split {α : Type} {l : list α} {p q : α → Prop} : l.countp p = (l.filter q).countp p + (l.filter (λ a, ¬ q a)).countp p :=
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
end list

namespace multiset
theorem countp_cons (s : multiset α) (a : α) (p : α → Prop) [∀ a, decidable (p a)] : countp p (a :: s) = ite (p a) 1 0 + countp p s :=
    by {by_cases p a; simp [h]}

theorem countp_false_eq_zero {s : multiset α} : s.countp (λ x, false) = 0 :=
    by {induction s; simp, induction s with x l ih, simp, simp [ih]}

theorem countp_eq_zero_of_false_of_mem {s : multiset α} {p : α → Prop} (h : ∀ x ∈ s, ¬ p x) : s.countp p = 0 :=
begin
  rcases s with s,
  simp * at *,
  revert h,
  induction s with x l ih; simp [list.countp_cons],
  intros hx hl,
  split,
  { exact ih hl, },
  { simp [hx], },
end

theorem countp_eq_card_of_true_of_mem {s : multiset α} {p : α → Prop} (h : ∀ x ∈ s, p x) : s.countp p = s.card :=
begin
  rcases s with l,
  simp * at *,
  revert h,
  induction l with x l ih; simp [list.countp_cons],
  intros hx hl,
  simp [hx, ih hl],
end

theorem countp_split {α : Type} (s : multiset α) {p : α → Prop} (q : α → Prop) : s.countp p = (s.filter q).countp p + (s.filter (λ a, ¬ q a)).countp p :=
begin
  rcases s with l,
  exact list.countp_split,
end

theorem not_mem_of_countp_eq_zero {α : Type} (s : multiset α) (p : α → Prop) : s.countp p = 0 ↔ ∀ a ∈ s, ¬ p a :=
begin
  rcases s with l,
  simp [list.not_mem_of_countp_eq_zero],
end
end multiset

namespace finset

@[simp]
def countp (p : α → Prop) [decidable_pred p] (s : finset α) : ℕ := s.val.countp p

theorem filter_eq_multiset_filter (p : α → Prop) [decidable_pred p] (s : finset α) : (s.filter p).val = s.val.filter p := by {rcases s, simp}

theorem multiset_card_eq_card (s : finset α) : s.val.card = s.card :=
by {rcases s, simp [card] }

lemma eq_of_subset_of_subset {s t : finset α} (h₁ : s ⊆ t) (h₂ : t ⊆ s) : s = t :=
(eq_of_subset_of_card_le h₁ (card_le_of_subset h₂))

end finset

namespace nat
@[simp]
theorem eq_of_succ_eq_succ (n m : ℕ) : n.succ = m.succ ↔ n = m := by {split, intro h, injection h, intro h, apply_fun nat.succ at h, exact h, }
@[simp]
theorem not_succ_eq_zero (n : ℕ) : n.succ ≠ 0 := by {intro h, injection h }
@[simp]
theorem not_zero_eq_succ (n : ℕ) : 0 ≠ n.succ := by {intro h, injection h }

@[simp]
theorem add_mul_mod (a b m : ℕ) : (a + m * b) % m = a % m := by simp

@[simp]
theorem add_mod_mod (a b m : ℕ) : (a + b % m) % m = (a + b) % m :=
begin
  conv in (a + b) {
    rw ← nat.mod_add_div b m,
  },
  rw ← nat.add_assoc,
  rw add_mul_mod,
end

@[simp]
theorem mod_add_mod (a b m : ℕ) : (a % m + b) % m = (a + b) % m :=
begin
  simp,
end

@[simp]
theorem even_of_not_odd (n : ℕ) : ¬ n % 2 = 1 ↔ n % 2 = 0 :=
begin
  have := nat.mod_two_eq_zero_or_one n,
  split; intro h; finish,
end

@[simp]
theorem odd_of_not_even (n : ℕ) : ¬ n % 2 = 0 ↔ n % 2 = 1 :=
begin
  have := nat.mod_two_eq_zero_or_one n,
  split; intro h; finish,
end

@[simp]
theorem one_mod_two_eq_one : 1 % 2 = 1 := nat.mod_eq_of_lt (by linarith)
@[simp]
theorem zero_mod_two_eq_zero : 0 % 2 = 0 := nat.mod_eq_of_lt (by linarith)

@[simp]
theorem even_of_succ_odd (n : ℕ) : (n + 1) % 2 = 1 ↔ n % 2 = 0 :=
begin
  rw ← mod_add_mod,
  split; intro h,
  { by_contradiction hn,
    simp at hn,
    simp [hn] at h,
    exact h, },
  simp [h],
end

@[simp]
theorem odd_of_succ_even (n : ℕ) : (n + 1) % 2 = 0 ↔ n % 2 = 1 :=
begin
  rw ← mod_add_mod,
  split; intro h,
  { by_contradiction hn,
    simp at hn,
    simp [hn] at h,
    exact h, },
  simp [h],
end
end nat

open multigraph
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
    rw @list.countp_split _ l1 _ (λ b, r a b),
    rw @list.countp_split _ l2 _ (λ b, r a b),
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
  set len := l1.length,
  exact injective_count_aux len nodup l1 l2 (by simp [len]),
end

lemma count_plus (l : list α) (p q : α → Prop) (nodup : ∀ a ∈ l, ¬ (p a ∧ q a)) :
l.countp p + l.countp q = l.countp (λ a, p a ∨ q a) :=
begin
  induction l with a l1 ih,
  { simp },
  simp [list.count_cons', list.countp_cons],
  by_cases p a ∨ q a,
  { cases h,
    { have : ¬ q a, by finish,
      simp [h, this], rw ih,
      intros a hmem, exact nodup a (by simp [hmem]),},
    { have : ¬ p a, by finish,
      simp [h, this], rw ih,
      intros a hmem, exact nodup a (by simp [hmem]),} },
  { have hane : ¬ p a, by finish,
    have hbne : ¬ q a, by finish,
    simp [hane, hbne], rw ih,
    intros a hmem, exact nodup a (by simp [hmem]),}
end

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

lemma degree_constraint_of_eulerian (h : g.is_eulerian) :
g.V.countp (λ v, g.degree v % 2 = 1) = 0 ∨ g.V.countp (λ v, g.degree v % 2 = 1) = 2 :=
begin
  rw is_eulerian at h,
  cases h with s h,
  cases h with t h,
  cases h with w he,
  unfold finset.countp,
  by_cases hcase : s = t,
  { left,
    have : ∀ v ∈ g.V, g.degree v % 2 = 0,
    { intros v hmem,
      have hcnt := vert_in_walk g v _ _ w,
      simp [hcase] at hcnt,
      rw degree_of_eulerian_walk _ he,
      by_cases htv : t = v; simp [htv] at hcnt; rw hcnt; ring; simp, },
      conv at this in (_ = 0) { rw ← nat.even_of_not_odd, },
      exact multiset.countp_eq_zero_of_false_of_mem this,
  },
  right,
  rw multiset.countp_split g.V.val (λ x, s = x ∨ t = x),
  simp,
  have : ∀ v ∈ g.V, ¬ (s = v ∨ t = v) → g.degree v % 2 = 0,
  { intros v hmem hne,
    rw not_or_distrib at hne,
    cases hne with hnes hnet,
    have hcnt := vert_in_walk g v _ _ w,
    rw degree_of_eulerian_walk _ he,
    simp [hnes, hnet] at hcnt,
    simp [hcnt],
    ring, simp, },
  have : ∀ v ∈ g.V, ¬ (degree g v % 2 = 1 ∧ ¬(s = v ∨ t = v)),
  { intros v hmem h,
    cases h with h hne,
    rw ← nat.odd_of_not_even at h,
    exact absurd (this v hmem hne) h,
  },
  suffices : multiset.countp (λ (a : α), degree g a % 2 = 1 ∧ (s = a ∨ t = a)) g.V.val +
      multiset.countp (λ (a : α), degree g a % 2 = 1 ∧ ¬(s = a ∨ t = a)) g.V.val =
    2,
  { convert this, },
  simp [multiset.countp_eq_zero_of_false_of_mem this],
  rw multiset.countp_eq_card_filter,
  rw ← finset.filter_eq_multiset_filter,

  have hsdeg : g.degree s % 2 = 1,
  { have hcnt := vert_in_walk g s _ _ w,
    simp [ne.symm hcase] at hcnt,
    rw degree_of_eulerian_walk _ he,
    simp [hcnt],
    ring, simp, },
  have htdeg : g.degree t % 2 = 1,
  { have hcnt := vert_in_walk g t _ _ w,
    simp [hcase] at hcnt,
    rw degree_of_eulerian_walk _ he,
    simp [eq.symm hcnt],
    ring, simp, },

  have : finset.filter (λ (a : α), degree g a % 2 = 1 ∧ (s = a ∨ t = a)) g.V = {s, t},
  { apply finset.eq_of_subset_of_subset; rw finset.subset_iff; intros x hmem,
    { rw finset.mem_filter at hmem,
    rcases hmem with ⟨hmem, hdeg, hcase | hcase⟩; simp [hcase],},
    { simp at hmem,
      cases hmem; rw hmem,
      { simp [htdeg, w.t_mem], },
      { simp [hsdeg, w.s_mem], }, },
  },
  rw this,
  rw finset.multiset_card_eq_card,
  simp,
  change s ≠ t at hcase,
  rw @finset.card_insert_of_not_mem _ _ t (finset.singleton s) (by simp [ne_comm.mp hcase]),
  simp [hcase],
end

namespace konigsberg

@[simp]
def V : finset ℕ := {0, 1, 2, 3}
@[simp]
def E : multiset (ℕ × ℕ) :=
    (0, 1) :: (0, 1) :: (1, 2) :: (1, 2) :: (0, 3) :: (1, 3) :: (2, 3) :: {}

lemma valid_edges : ∀ e : ℕ × ℕ, e ∈ E → e.1 ∈ V ∧ e.2 ∈ V :=
begin
  intros e hmem,
  rw V,
  rw E at hmem,
  fin_cases hmem; simp,
end

lemma no_self_loops : ∀ u v : ℕ, (u, v) ∈ E → u ≠ v :=
begin
  intros u v hmem heq,
  rw heq at hmem,
  rw E at hmem,
  fin_cases hmem; simp at hmem; finish,
end

@[simp]
def G := multigraph.mk V E valid_edges no_self_loops

lemma all_degrees_odd : ∀ v ∈ G.V, G.degree v % 2 = 1 :=
begin
  intros v hmem,
  simp at hmem,
  rcases hmem with rfl | rfl | rfl | rfl; unfold degree; simp,
end

lemma four_odd_degree_verts : G.V.countp (λ v, G.degree v % 2 = 1) = 4 :=
begin
  unfold finset.countp,
  rw multiset.countp_eq_card_of_true_of_mem,
  { simp, },
  exact all_degrees_odd,
end

theorem no_euler_walk_in_konigsberg_bridge : ¬ G.is_eulerian :=
begin
  intro h,
  have hdeg := degree_constraint_of_eulerian _ h,
  rw four_odd_degree_verts at hdeg,
  simp at hdeg,
  exact hdeg,
end

end konigsberg