import Mathlib

namespace KnotTheory

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

structure PrePLLink (E : Type*) [AddCommGroup E] [Module ℝ E] where
  next : Equiv.Perm E
  V : Finset E
  fix : ∀ p : E, (p ∈ V) ↔ (next p ≠ p)

def LinkFunction (L : PrePLLink E) : E × ℝ → E :=
  fun (P, t) ↦ (1 - t) • P + t • (L.next P)

def InCO (t : ℝ) : Prop := 0 ≤ t ∧ t < 1



structure PLLink (E : Type*) [AddCommGroup E] [Module ℝ E] extends PrePLLink E where
  injection : ∀ P ∈ V, ∀ Q ∈ V, ∀t₁ t₂ : ℝ,
    InCO t₁ ∧ InCO t₂ →
    LinkFunction toPrePLLink (P, t₁) =
    LinkFunction toPrePLLink (Q, t₂) → (P = Q ∧ t₁ = t₂)

instance : Coe (PLLink E) (PrePLLink E) where
  coe L := L.toPrePLLink

lemma Link.func_inj_in_v (L : PLLink E) :
  ∀ P ∈ L.V, ∀ Q ∈ L.V, ∀t₁ t₂ : ℝ,
  (InCO t₁) → (InCO t₂) →
  (LinkFunction L (P, t₁) = LinkFunction L (Q, t₂)) → P = Q := by
    intro P hP Q hQ u v hu hv h
    have eqs : (P = Q) ∧ (u = v) := by
      apply L.injection
      repeat assumption
      constructor
      · exact hu
      · exact hv
      exact h
    exact eqs.1


lemma Link.vertex_repr (L : PrePLLink E) :
  ∀ A ∈ L.V, A = LinkFunction L (A, 0) := by
    intro A hA
    unfold LinkFunction
    simp

@[simp]
lemma Link.not_vertex_is_fix (L : PrePLLink E) :
  ∀ p : E, p ∉ L.V → (L.next p = p) := by
    intro p hp
    by_contra h
    exact hp ((L.fix p).mpr h)

lemma Link.next_closed (L : PrePLLink E) :
  ∀ A ∈ L.V, L.next A ∈ L.V := by
  intro A hA
  by_contra h
  have h' : L.next (L.next A) = L.next A := by
    by_contra hN
    apply (L.fix (L.next A)).mpr at hN
    contradiction
  have h'' : L.next⁻¹ (L.next (L.next A)) = L.next⁻¹ (L.next A) := by
    rw [h']
  simp at h''
  rw [h''] at h
  contradiction

lemma Link.InCOZero : InCO 0 := by
  unfold InCO
  grind

lemma Link.notInCOOne : ¬InCO 1 := by
  unfold InCO
  intro h
  grind

lemma Link.next_inv_closed (L : PrePLLink E) :
  ∀ A ∈ L.V, L.next⁻¹ A ∈ L.V := by
    intro A hA
    by_contra h
    have h' := Link.not_vertex_is_fix L (L.next⁻¹ A) h
    rw [←h'] at h
    simp at h
    contradiction

lemma Link.if_next_vert_then_vert (L : PrePLLink E) :
  ∀ A : E, L.next A ∈ L.V → A ∈ L.V := by
    intro A hA
    apply Link.next_inv_closed at hA
    simp at hA
    exact hA

lemma Link.next_not_repr_with_vert (L : PLLink E) :
  ∀ A ∈ L.V, ∀ t : ℝ, (InCO t) →  L.next A ≠ LinkFunction L (A, t) := by
    intro A hA t ht
    by_contra eq
    rw [Link.vertex_repr L.toPrePLLink (L.next A) (Link.next_closed L.toPrePLLink A hA)] at eq
    have h : (L.next A = A) ∧ (0 = t) := by
      apply L.injection
      apply Link.next_closed
      exact hA
      exact hA
      constructor
      · exact Link.InCOZero
      · exact ht
      exact eq
    have h_1 := h.1
    have h_2 := (L.fix A).mp hA
    contradiction


lemma Link.seg_not_vert (L : PLLink E) :
  ∀ A ∈ L.V, ∀ t : ℝ, (InCO t) → (t ≠ 0) →
  LinkFunction L (A, t) ∉ L.V := by
    intro A hA t ht htnz
    by_contra in_v
    let Q := LinkFunction L (A, t)
    have hQ : Q = LinkFunction L (A, t) := by rfl
    rw [Link.vertex_repr L Q in_v] at hQ
    have h : (Q = A) ∧ (0 = t) := by
      apply L.injection
      exact in_v
      exact hA
      constructor
      · exact Link.InCOZero
      · exact ht
      exact hQ
    rw [h.2] at htnz
    contradiction

lemma Link.next_simp_nz (L : PLLink E) :
  ∀ Q ∈ L.V, ∀ t : ℝ, (InCO t) → (t ≠ 0) →
  L.next (LinkFunction L (Q, t)) = LinkFunction L (Q, t) := by
    intro Q hQ t ht htnz
    apply Link.not_vertex_is_fix
    apply Link.seg_not_vert
    exact hQ
    exact ht
    exact htnz

lemma Link.next_simp_z (L : PLLink E) :
  ∀ Q ∈ L.V, ∀ t : ℝ, (InCO t) → (t = 0) →
  (L.next (LinkFunction L (Q, t)) = L.next Q) := by
    intro Q hQ t ht htz
    simp
    rw [htz]
    unfold LinkFunction
    simp

lemma lin_comb_linkfunc_next (L : PLLink E) :
  ∀ Q ∈ L.V, ∀ u t : ℝ,
  (1 - u) • (LinkFunction L (Q , t)) + u • (L.next Q) =
  LinkFunction L (Q, u + t - u * t) := by
    intro Q hQ u t
    unfold LinkFunction
    simp
    module

lemma cond_linkfunc_next (u t : ℝ) :
  (InCO u) → (InCO t) → InCO (u + t - u * t) := by
  intro hu ht
  unfold InCO at *
  aesop
  · nlinarith
  · nlinarith


lemma lin_comb_vert_linkfunc (L : PLLink E) :
  ∀ Q ∈ L.V, ∀ u t : ℝ,
  (1 - u) • Q + u • (LinkFunction L (Q, t)) =
  LinkFunction L (Q, u * t) := by
    intro Q hQ u t
    unfold LinkFunction
    simp
    module

lemma cond_vert_linkfunc (u t : ℝ) :
  (InCO u) → (InCO t) → InCO (u * t) := by
  intro hu ht
  unfold InCO at *
  aesop
  · nlinarith
  · nlinarith

lemma link_func_inj_in_t (L : PLLink E) :
  ∀ Q ∈ L.V, ∀ u t : ℝ,
  LinkFunction L (Q, u) = LinkFunction L (Q, t) → u = t := by
    intro Q hQ u t hut
    unfold LinkFunction at hut
    simp at hut
    rw [←sub_eq_zero] at hut
    have h : (t - u) • (Q - L.next Q) = 0 := by
      rw [←hut]
      module
    simp at h
    rcases h with h₁ | h₂
    · rw [sub_eq_zero] at h₁
      rw [h₁]
    · rw [sub_eq_zero] at h₂
      symm at h₂
      exfalso
      exact (L.fix Q).mp hQ h₂

lemma uv_1 (u v t : ℝ) :
  (InCO u) → (InCO v) → (InCO t) → (t ≠ 0) →
  (u + t - u * t = v * t) → (v = 1) := by
  intro hu hv ht htnz h
  unfold InCO at *
  have h' : u * (1 - t) = - (1 - v) * t := by
    ring_nf
    nth_rw 2 [mul_comm]
    rw [←h]
    ring
  have ineq₁ : 0 ≤ u * (1 - t) := by
    exact mul_nonneg hu.1 (by linarith)
  have ineq₂ :  0 ≤ (1 - v) * t := by
    exact mul_nonneg (by linarith) ht.1
  rw [h'] at ineq₁
  have eq' : 0 = (1 - v) * t := by
    apply le_antisymm
    exact ineq₂
    linarith
  apply neg_le_neg at ineq₁
  simp at eq'
  rcases eq' with c₁ | c₂
  · linarith
  · contradiction

lemma uv_2 (u v t : ℝ) :
  (InCO t) →
  (u + t - u * t = v + t - v * t) →
  u = v := by
  intro ht h
  unfold InCO at ht
  have ht1 := ht.1
  have ht2 := ht.2
  have eq : (u - v) * (1 - t) = 0 := by
    nlinarith
  simp at eq
  rcases eq with c₁ | c₂
  · linarith
  · linarith






-- To-do: replace long sequences of "exact" with "repeat assumption"

/--
(1) We may subdivide an edge, AB, in space of K into two edges, AC, CB,
 by placing a point C on the edge AB.
-/
def SubdivideAt [DecidableEq E] (L : PLLink E) (A : E)
  (hA : A ∈ L.V)
  (t : ℝ) (ht : InCO t) : PLLink E :=
  let C := LinkFunction L.toPrePLLink (A, t)
  {
    next := Equiv.trans (Equiv.swap A C) L.next
    V := insert C L.V
    fix := by
      intro p
      aesop
      · have h : L.next A ∈ L.V := by
          apply Link.next_closed
          exact hA
        rw [Link.vertex_repr L.toPrePLLink (L.next A) h] at a_1
        have h0 : InCO 0 := by
          unfold InCO
          constructor
          trivial
          linarith
        have h' : L.next A = A :=
          (L.injection (L.next A) h A hA 0 t ⟨h0, ht⟩ a_1).1
        have h'' : L.next A ≠ A :=
          (L.fix A).mp hA
        contradiction
      · apply (Equiv.eq_symm_apply _).mpr at a_1
        let q := (Equiv.symm L.next) p
        have hq : L.next⁻¹ p = q := by rfl
        have qV : q ∈ L.V := by
          rw [←hq]
          apply Link.next_inv_closed
          exact hA
        change LinkFunction L.toPrePLLink (p, t) = q at a_1
        apply_fun L.next at hq
        simp at hq
        rw [Link.vertex_repr L.toPrePLLink q] at a_1
        have eqs : (p = q) ∧ (t = 0) := by
          apply L.injection
          exact hA
          exact qV
          constructor
          · exact ht
          · unfold InCO
            grind
          exact a_1
        rw [eqs.1] at hq
        apply (L.fix q).mp at qV
        symm at hq
        contradiction
        exact qV
      · have h' : L.next A ∈ L.V := by
          exact Link.next_closed L.toPrePLLink A hA
        rw [Link.vertex_repr L.toPrePLLink (L.next A)] at a_1
        have eqs : (L.next A = A ∧ 0 = t) := by
          apply L.injection
          exact h'
          exact hA
          constructor
          · unfold InCO
            grind
          · exact ht
          exact a_1
        exact (L.fix A).mp hA eqs.1
        exact h'
      · exact (L.fix p).mp h_1 a_1
      · exact (L.fix p).mpr a
    injection := by
      intro P hP Q hQ u v huv
      unfold LinkFunction
      aesop
      · by_contra uv_neq
        rw [←sub_eq_zero] at a
        have h : (u - v) • (LinkFunction L.toPrePLLink (A, t) - L.next A) = -0 := by
          rw [←a]
          module
        simp at h
        have uv_neq0 : u - v ≠ 0 := by
          by_contra eq
          rw [sub_eq_zero] at eq
          rw [eq] at uv_neq
          contradiction
        rcases h with h₁ | h₂
        · contradiction
        · rw [sub_eq_zero] at h₂
          symm at h₂
          exact Link.next_not_repr_with_vert L A hA t ht h₂
      · by_cases h : t = 0
        · rw [h]
          unfold LinkFunction
          simp
        · have eq : L.next (LinkFunction L.toPrePLLink (Q, t)) = LinkFunction L.toPrePLLink (Q, t) := by
            apply Link.not_vertex_is_fix L.toPrePLLink (LinkFunction L.toPrePLLink (Q, t))
            apply Link.seg_not_vert
            exact hA
            exact ht
            exact h
          rw [eq] at a
          rw [lin_comb_linkfunc_next] at a
          rw [lin_comb_vert_linkfunc] at a
          have param_eq : u + t - u * t = v * t := by
            apply link_func_inj_in_t L Q hA
            exact a
          unfold InCO at *
          have h' : u * (1 - t) = - (1 - v) * t := by
            ring_nf
            nth_rw 2 [mul_comm]
            rw [←param_eq]
            ring
          have ineq₁ : 0 ≤ u * (1 - t) := by
            exact mul_nonneg left.1 (by linarith)
          have ineq₂ :  0 ≤ (1 - v) * t := by
            exact mul_nonneg (by linarith) ht.1
          rw [h'] at ineq₁
          have eq' : 0 = (1 - v) * t := by
            apply le_antisymm
            exact ineq₂
            apply neg_le_neg at ineq₁
            linarith
          simp at eq'
          rcases eq' with c₁ | c₂
          rw [sub_eq_zero] at c₁
          rw [←c₁] at right
          have right2 := right.2
          simp at right2
          contradiction
          exact hA
          exact hA
      · rw [lin_comb_linkfunc_next] at a
        change LinkFunction L.toPrePLLink (A, u + t - u * t) = LinkFunction L (Q, v) at a
        have eqs : (A = Q) ∧ (u + t - u * t = v) := by
          apply L.injection
          exact hA
          exact h_2
          constructor
          · apply cond_linkfunc_next
            exact left
            exact ht
          · exact right
          exact a
        rw [eqs.1] at h
        contradiction
        exact hA
      · rw [lin_comb_linkfunc_next] at a
        by_cases h : t = 0
        · rw [h] at a
          rw [←(Link.vertex_repr L Q hA)] at a
          simp at a
          change LinkFunction L (Q, u) = LinkFunction L (Q, v) at a
          apply link_func_inj_in_t L Q hA
          exact a
        · have not_vert : LinkFunction L (Q, t) ∉ L.V := by
            apply Link.seg_not_vert
            exact hA
            exact ht
            exact h
          rw [Link.not_vertex_is_fix] at a
          rw [lin_comb_vert_linkfunc] at a
          have eq : u + t - u * t = v * t := by
            apply link_func_inj_in_t L Q
            exact hA
            exact a
          have hv : v = 1 := by
            exact uv_1 u v t left right ht h eq
          rw [hv] at right
          exfalso
          exact Link.notInCOOne right
          exact hA
          exact not_vert
        · exact hA
      · rw [lin_comb_linkfunc_next] at a
        rw [lin_comb_linkfunc_next] at a
        have eq : u + t - u * t = v + t - v * t := by
          apply link_func_inj_in_t L A
          exact hA
          exact a
        have eq' : u = v := uv_2 u v t ht eq
        exact eq'
        exact hA
        exact hA
      · rw [lin_comb_linkfunc_next] at a
        change LinkFunction L (A, u + t - u * t) = LinkFunction L (Q, v) at a
        have eqs : (A = Q) ∧ (u + t - u * t = v) := by
          apply L.injection
          exact hA
          exact h_2
          constructor
          · exact cond_linkfunc_next u t left ht
          · exact right
          exact a
        rw [eqs.1] at h
        contradiction
        exact hA
      · by_cases ht' : t = 0
        · rw [ht']
          unfold LinkFunction
          simp
        · have not_vert : LinkFunction L (P, t) ∉ L.V := by
            apply Link.seg_not_vert
            exact hA
            exact ht
            exact ht'
          rw [Link.not_vertex_is_fix] at a
          rw [lin_comb_linkfunc_next] at a
          rw [lin_comb_vert_linkfunc] at a
          have eq : u * t = v + t - v * t := by
            apply link_func_inj_in_t L P
            exact hA
            exact a
          symm at eq
          have hu : u = 1 := by
            apply uv_1 v u t
            repeat assumption
          rw [hu] at left
          exfalso
          exact Link.notInCOOne left
          repeat assumption
      · rw [lin_comb_linkfunc_next] at a
        change LinkFunction L (P, u) = LinkFunction L (A, v + t - v * t) at a
        have eqs : (P = A ∧ u = v + t - v * t) := by
          apply L.injection
          exact h_1
          exact hA
          constructor
          · exact left
          · exact cond_linkfunc_next v t right ht
          exact a
        rw [eqs.1] at h
        contradiction
        exact hA
      · rw [lin_comb_linkfunc_next] at a
        by_cases ht' : t = 0
        · rw [Link.next_simp_z] at a
          change LinkFunction L (P, u) = LinkFunction L (P, v + t - v * t) at a
          rw [ht'] at a
          simp at a
          apply link_func_inj_in_t L P
          repeat assumption
        · rw [Link.next_simp_nz] at a
          rw [lin_comb_vert_linkfunc] at a
          have eq : u * t = v + t - v * t := by
            apply link_func_inj_in_t L P
            repeat assumption
          symm at eq
          have hu : u = 1 := by
            apply uv_1 v u t
            repeat assumption
          rw [hu] at left
          exfalso
          exact Link.notInCOOne left
          repeat assumption
        repeat assumption
      · rw [lin_comb_linkfunc_next] at a
        rw [lin_comb_linkfunc_next] at a
        have eq : u + t - u * t = v + t - v * t := by
          apply link_func_inj_in_t L A
          repeat assumption
        apply uv_2 u v t
        repeat assumption
      · rw [lin_comb_linkfunc_next] at a
        change LinkFunction L (P, u) = LinkFunction L (A, v + t - v * t) at a
        have eq : (P = A) ∧ (u = v + t - v * t) := by
          apply L.injection
          repeat assumption
          constructor
          · exact left
          · exact cond_linkfunc_next v t right ht
          exact a
        rw [eq.1] at h
        contradiction
        repeat assumption
      · by_cases ht : t = 0
        · rw [ht] at h_3
          rw [←Link.vertex_repr] at h_3
          contradiction
          repeat assumption
        · rw [Link.next_simp_nz] at a
          rw [lin_comb_vert_linkfunc] at a
          rw [lin_comb_linkfunc_next] at a
          have eq : u * t = v + t - v * t := by
            apply link_func_inj_in_t L P
            repeat assumption
          symm at eq
          have eq' : u = 1 := by
            apply uv_1 v u t
            repeat assumption
          rw [eq'] at left
          exfalso
          exact Link.notInCOOne left
          repeat assumption
      · by_cases ht : t = 0
        · rw [Link.next_simp_z] at a
          change LinkFunction L (P, u) = LinkFunction L (Q, v) at a
          have eq : (P = Q) ∧ (u = v) := by
            apply L.injection
            repeat assumption
            constructor
            · assumption
            · assumption
            exact a
          exact eq.1
          repeat assumption
        · rw [Link.next_simp_nz] at a
          rw [lin_comb_vert_linkfunc] at a
          change LinkFunction L (P, u * t) = LinkFunction L (Q, v) at a
          have eq : (P = Q) ∧ (u * t = v) := by
            apply L.injection
            repeat assumption
            constructor
            · (expose_names; exact cond_vert_linkfunc u t left ht_1)
            · exact right
            exact a
          exact eq.1
          repeat assumption
      · by_cases ht' : t = 0
        · rw [ht'] at h
          rw [←Link.vertex_repr] at h
          contradiction
          exact hA
        · have h_1' : LinkFunction L (Q, t) ∉ L.V := by
            exact Link.seg_not_vert L Q hA t ht ht'
          contradiction
      · have htnz : t ≠ 0 := by
          by_contra htz
          rw [htz] at h
          rw [←Link.vertex_repr] at h
          contradiction
          exact hA
        have h_1' : LinkFunction L (A, t) ∉ L.V := by
          exact Link.seg_not_vert L A hA t ht htnz
        contradiction
      · by_cases ht' : t = 0
        · rw [Link.next_simp_z] at a
          change LinkFunction L (P, u) = LinkFunction L (Q, v) at a
          apply Link.func_inj_in_v at a
          rw [a] at h
          contradiction
          repeat assumption
        · rw [Link.next_simp_nz] at a
          rw [lin_comb_vert_linkfunc] at a
          change LinkFunction L (P, u) = LinkFunction L (Q, v * t) at a
          have hvt : InCO (v * t) := by
            exact cond_vert_linkfunc v t right ht
          apply Link.func_inj_in_v at a
          rw [a] at h
          contradiction
          repeat assumption
      · have htnz : t ≠ 0 := by
          by_contra htz
          rw [htz] at h_4
          rw [←Link.vertex_repr] at h_4
          contradiction
          repeat assumption
        have h_2' : LinkFunction L (A, t) ∉ L.V := by
          exact Link.seg_not_vert L A hA t ht htnz
        contradiction
      · change LinkFunction L (P, u) = LinkFunction L (Q, v) at a
        apply Link.func_inj_in_v L at a
        repeat assumption
      · by_cases ht' : t = 0
        · rw [Link.next_simp_z] at a
          change LinkFunction L (Q, u) = LinkFunction L (Q, v) at a
          apply link_func_inj_in_t L at a
          repeat assumption
        · rw [Link.next_simp_nz] at a
          rw [lin_comb_vert_linkfunc] at a
          rw [lin_comb_vert_linkfunc] at a
          apply link_func_inj_in_t L at a
          simp at a
          rcases a with c₁ | c₂
          · exact c₁
          · contradiction
          repeat assumption
      · have htnz : t ≠ 0 := by
          by_contra htz
          rw [htz] at h_3
          rw [←Link.vertex_repr] at h_3
          contradiction
          exact hA
        have h_3' : LinkFunction L (P, t) ∉ L.V := by
          exact Link.seg_not_vert L P hA t ht htnz
        contradiction
      · by_cases ht' : t = 0
        · rw [Link.next_simp_z] at a
          change LinkFunction L (P, u) = LinkFunction L (Q, v) at a
          apply Link.func_inj_in_v L at a
          rw [a] at h_3
          contradiction
          repeat assumption
        · rw [Link.next_simp_nz] at a
          rw [lin_comb_vert_linkfunc] at a
          change LinkFunction L (P, u * t) = LinkFunction L (Q, v) at a
          apply Link.func_inj_in_v L at a
          rw [a] at h_3
          contradiction
          repeat assumption
          exact cond_vert_linkfunc u t left ht
          repeat assumption
      · have htnz : t ≠ 0 := by
          by_contra htz
          rw [htz] at h
          rw [←Link.vertex_repr] at h
          contradiction
          exact hA
        have h_1' : LinkFunction L (Q, t) ∉ L.V := by
          exact Link.seg_not_vert L Q hA t ht htnz
        contradiction
      · have htnz : t ≠ 0 := by
          by_contra htz
          rw [htz] at h_4
          rw [←Link.vertex_repr] at h_4
          contradiction
          exact hA
        have h_4' : LinkFunction L (A, t) ∉ L.V := by
          exact Link.seg_not_vert L A hA t ht htnz
        contradiction
      · have htnz : t ≠ 0 := by
          by_contra htz
          rw [htz] at h
          rw [←Link.vertex_repr] at h
          contradiction
          exact hA
        have h_1' : LinkFunction L (A, t) ∉ L.V := by
          exact Link.seg_not_vert L A hA t ht htnz
        contradiction
      · by_cases ht' : t = 0
        · rw [Link.next_simp_z] at a
          change LinkFunction L (P, u) = LinkFunction L (Q, v) at a
          apply Link.func_inj_in_v at a
          rw [a] at h
          contradiction
          repeat assumption
        · rw [Link.next_simp_nz] at a
          rw [lin_comb_vert_linkfunc] at a
          change LinkFunction L (P, u) = LinkFunction L (Q, v * t) at a
          apply Link.func_inj_in_v at a
          rw [a] at h
          contradiction
          repeat assumption
          exact cond_vert_linkfunc v t right ht
          repeat assumption
      · have htnz : t ≠ 0 := by
          by_contra htz
          rw [htz] at h_4
          rw [←Link.vertex_repr] at h_4
          contradiction
          exact hA
        have h_1' : LinkFunction L (A, t) ∉ L.V := by
          exact Link.seg_not_vert L A hA t ht htnz
        contradiction
      · change LinkFunction L (P, u) = LinkFunction L (Q, v) at a
        have eqs : (P = Q) ∧ (u = v) := by
          apply L.injection
          repeat assumption
          constructor
          · exact left
          · exact right
          exact a
        exact eqs.2

  }


lemma Link.no_two_cycles (L : PLLink E) :
  ∀ Q ∈ L.V, L.next (L.next Q) ≠ Q := by
    intro Q hQ
    by_contra
    have mid_eq : LinkFunction L (Q, 0.5) = LinkFunction L (L.next Q, 0.5) := by
      unfold LinkFunction
      grind
    have h : InCO 0.5 := by
      unfold InCO
      grind
    apply Link.func_inj_in_v at mid_eq
    symm at mid_eq
    exact (L.fix Q).mp hQ mid_eq
    exact hQ
    exact next_closed L.toPrePLLink Q hQ
    repeat assumption


/--
[The converse of (1)] If AC and CB are two adjacent edges of
K such that if C is erased AB becomes a straight line, then we
may remove the point C.
-/
-- Removes the focus if it would lie in the segment between
-- the previous and next vertices.
def EraseAt [DecidableEq E] (L : PLLink E) (A : E)
  (hA : A ∈ L.V)
  (t : ℝ) (ht : InCO t) (C : L.V) (hC : C = L.next A)
  (hCol : C = LinkFunction L (A, t)) : PLLink E := {

  next := Equiv.trans (Equiv.swap A C) L.next
  V := L.V.erase C
  fix := by
    intro p
    aesop
    · have hnp : L.next (L.next p) ≠ p := by
        exact Link.no_two_cycles L p hA
      contradiction
    · exact (L.fix p).mp right a
    · exact (L.fix p).mpr a
  injection := by
    intro P hP Q hQ u v huv heq
    unfold LinkFunction at heq
    simp at heq
    aesop
    · rw [←hC] at property
      have ht' : t ≠ 0 := by
        by_contra htz
        rw [htz] at hC
        rw [←Link.vertex_repr] at hC
        contradiction
        exact hA
      have property' : LinkFunction L (P, t) ∉ L.V := by
        exact Link.seg_not_vert L P hA t ht ht'
      contradiction
    · have hC' : L.next Q ≠ LinkFunction L (Q, t) := by
        exact Link.next_not_repr_with_vert L Q hA t ht
      symm at hC
      contradiction
    · have hC' : L.next A ≠ LinkFunction L (A, t) := by
        exact Link.next_not_repr_with_vert L A hA t ht
      symm at hC
      contradiction
    · have hC' : L.next Q ≠ LinkFunction L (Q, t) := by
        exact Link.next_not_repr_with_vert L Q hA t ht
      symm at hC
      contradiction
    · have hC' : L.next P ≠ LinkFunction L (P, t) := by
        exact Link.next_not_repr_with_vert L P hA t ht
      symm at hC
      contradiction
    · have hC' : L.next Q ≠ LinkFunction L (Q, t) := by
        exact Link.next_not_repr_with_vert L Q hA t ht
      symm at hC
      contradiction
    · have hC' : L.next A ≠ LinkFunction L (A, t) := by
        exact Link.next_not_repr_with_vert L A hA t ht
      symm at hC
      contradiction


}

-- The point C lies in link K.
def LiesInLink (C : E) (L : PLLink E) : Prop :=
  ∃P ∈ L.V, ∃t : ℝ, InCO t ∧ (LinkFunction L (P, t) = C)

-- An auxiliary function to represent points in a triangle.
def Link.TriFunc (L : PLLink E)
  (A : E) (p : ℝ) (C : E) (q : ℝ) :=
  (1 - q) • (LinkFunction L (A, p)) + q • C

notation L "⟨" A "," p ";" C "," q "⟩" => Link.TriFunc L A p C q

-- The triangle A - C - next(A) only intersects K at A - next(A), with
-- C not in the link.
def NonIntersectingTriangle (L : PLLink E) (A : E) (C : E) : Prop :=
  ∀p ∈ Set.Icc 0 1, ∀q ∈ Set.Icc 0 1, LiesInLink (L⟨A, p; C, q⟩) L → (q = 0)


lemma tri_func_c_zero (L : PLLink E)
  (A : E) (p : ℝ) (C : E) :
    L⟨A, p; C, 0⟩ = LinkFunction L (A, p) := by
    unfold Link.TriFunc
    simp

lemma tri_func_zero_one (L : PLLink E)
  (A : E) (C : E) :
    L⟨A, 0; C, 1⟩ = C := by
    unfold Link.TriFunc
    simp

-- The non-intersecting triangle condition implies that C is not in the link.
lemma non_inter_tri_not_in (L : PLLink E) :
  ∀P ∈ L.V, ∀ C : E, (NonIntersectingTriangle L P C) → ¬LiesInLink C L := by
    intro P hP C hT
    by_contra lies_in_link
    obtain ⟨Q, hQ, t, ht1, ht2⟩ := lies_in_link
    have h : LiesInLink (L⟨P, 0; C, 1⟩) L := by
      unfold LiesInLink
      use Q
      constructor
      · exact hQ
      · use t
        constructor
        · exact ht1
        · rw [tri_func_zero_one L]
          exact ht2
    have in0 : (0 : ℝ) ∈ Set.Icc 0 1 := by
      simp
    have in1 : (1 : ℝ) ∈ Set.Icc 0 1 := by
      simp
    have one_eq_zero : (1 : ℝ) = 0 := by
      apply hT
      exact in0
      exact in1
      exact h
    simp at one_eq_zero


lemma verts_lie_in_link (L : PLLink E) :
  ∀P ∈ L.V, LiesInLink P L := by
  intro P hP
  use P ; use hP ; use 0
  constructor
  · exact Link.InCOZero
  · exact Eq.symm (Link.vertex_repr L.toPrePLLink P hP)

-- The non-intersecting triangle condition implies that C is not a vertex.
lemma non_inter_tri_not_vert (L : PLLink E) :
  ∀P ∈ L.V, ∀C : E, (NonIntersectingTriangle L P C) → (C ∉ L.V) := by
    intro P hP C hT
    by_contra hC
    have h1 : LiesInLink C L := by
      apply verts_lie_in_link
      exact hC
    have h2 : ¬LiesInLink C L := by
      apply non_inter_tri_not_in L P hP
      exact hT
    contradiction

-- Note: Most of the NIT lemmas were provided by
-- Aristotle, along with the proof of 'injection' in AddAt.
lemma NIT.inj_at_Q_next (L : PLLink E) (u v : ℝ) :
  ∀A ∈ L.V, ∀ Q : E, NonIntersectingTriangle L A Q →
  ((1 - u) • Q + u • L.next A = (1 - v) • Q + v • L.next A) →
  (u = v) := by
  intro A hA Q hQ heq
  have eq' : (u - v) • (L.next A - Q) = 0 := by
    rw [←sub_eq_zero] at heq
    rw [←heq]
    module
  simp at eq'
  rcases eq' with c₁ | c₂
  · rw [sub_eq_zero] at c₁
    exact c₁
  · rw [sub_eq_zero] at c₂
    apply non_inter_tri_not_in at hQ
    have h : LiesInLink Q L := by
      apply verts_lie_in_link
      rw [←c₂]
      apply Link.next_closed
      exact hA
    contradiction
    exact hA

lemma NIT.addAt_ac_inj (L : PLLink E) (A C : E)
    (hA : A ∈ L.V) (hT : NonIntersectingTriangle L A C)
    {u v : ℝ}
    (h : (1 - u) • A + u • C = (1 - v) • A + v • C) : u = v := by
  have hCA : C ≠ A := by
    intro hCA
    have hC : C ∈ L.V := by simpa [hCA] using hA
    exact non_inter_tri_not_vert L A hA C hT hC
  have hz : (u - v) • (C - A) = 0 := by
    rw [← sub_eq_zero] at h
    rw [← h]
    module
  rcases smul_eq_zero.mp hz with huv | hzero
  · exact sub_eq_zero.mp huv
  · exact (hCA (sub_eq_zero.mp hzero)).elim

lemma NIT.addAt_cb_inj (L : PLLink E) (A C : E)
    (hA : A ∈ L.V) (hT : NonIntersectingTriangle L A C)
    {u v : ℝ}
    (h : (1 - u) • C + u • L.next A =
      (1 - v) • C + v • L.next A) : u = v := by
  have hCB : C ≠ L.next A := by
    intro hCB
    have hC : C ∈ L.V := by
      rw [hCB]
      exact Link.next_closed L.toPrePLLink A hA
    exact non_inter_tri_not_vert L A hA C hT hC
  have hz : (u - v) • (L.next A - C) = 0 := by
    rw [← sub_eq_zero] at h
    rw [← h]
    module
  rcases smul_eq_zero.mp hz with huv | hzero
  · exact sub_eq_zero.mp huv
  · exact (hCB (sub_eq_zero.mp hzero).symm).elim

lemma NIT.addAt_ac_eq_old (L : PLLink E) (A C P : E)
    (hA : A ∈ L.V) (hP : P ∈ L.V) (hT : NonIntersectingTriangle L A C)
    {u v : ℝ} (hu : InCO u) (hv : InCO v)
    (h : (1 - u) • A + u • C = LinkFunction L (P, v)) :
    A = P ∧ u = v := by
  have huIcc : u ∈ Set.Icc (0 : ℝ) 1 := ⟨hu.1, le_of_lt hu.2⟩
  have hzero : u = 0 := by
    apply hT 0 (by simp) u huIcc
    exact ⟨P, hP, v, hv, by simpa [Link.TriFunc, LinkFunction] using h.symm⟩
  have hold : LinkFunction L (A, 0) = LinkFunction L (P, v) := by
    simpa [hzero, LinkFunction] using h
  have hi := L.injection A hA P hP 0 v ⟨Link.InCOZero, hv⟩ hold
  exact ⟨hi.1, by simpa [hzero] using hi.2⟩

lemma NIT.addAt_cb_ne_old (L : PLLink E) (A C P : E)
    (hP : P ∈ L.V) (hT : NonIntersectingTriangle L A C)
    {u v : ℝ} (hu : InCO u) (hv : InCO v) :
    (1 - u) • C + u • L.next A ≠ LinkFunction L (P, v) := by
  intro h
  have hqIcc : 1 - u ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hu.1, hu.2]
  have hqzero : 1 - u = 0 := by
    apply hT 1 (by simp) (1 - u) hqIcc
    refine ⟨P, hP, v, hv, ?_⟩
    simpa [Link.TriFunc, LinkFunction, add_comm] using h.symm
  exact (ne_of_lt hu.2) (by linarith)

lemma NIT.addAt_ac_ne_cb (L : PLLink E) (A C : E)
    (hA : A ∈ L.V) (hT : NonIntersectingTriangle L A C)
    {u v : ℝ} (hu : InCO u) (hv : InCO v) :
    (1 - u) • A + u • C ≠ (1 - v) • C + v • L.next A := by
  intro h
  have hnext : L.next A ∈ L.V := Link.next_closed L.toPrePLLink A hA
  have hAne : A ≠ L.next A := by
    intro heq
    exact (L.fix A).mp hA heq.symm
  rcases lt_trichotomy (u + v) 1 with hsum | hsum | hsum
  · let q : ℝ := (1 - u - v) / (1 - u)
    have hden : 0 < 1 - u := by linarith [hu.2]
    have hqpos : 0 < q := by
      dsimp [q]
      exact div_pos (by linarith) hden
    have hqle : q ≤ 1 := by
      dsimp [q]
      apply (div_le_one hden).2
      linarith [hv.1]
    have hqeq : (1 - u) * q = 1 - u - v := by
      dsimp [q]
      field_simp [ne_of_gt hden]
    have htri : L⟨A, 1; C, q⟩ = A := by
      have hone : 1 - u ≠ 0 := ne_of_gt hden
      have hlin : (1 - u) • A = (1 - u - v) • C + v • L.next A := by
        calc
          _ = ((1 - u) • A + u • C) - u • C := by module
          _ = ((1 - v) • C + v • L.next A) - u • C := by rw [h]
          _ = _ := by module
      have hqeq' : (1 - u) * (1 - q) = v := by linarith [hqeq]
      have hz : (1 - u) • (L⟨A, 1; C, q⟩ - A) = 0 := by
        dsimp [Link.TriFunc, LinkFunction]
        simp only [sub_self, zero_smul, zero_add, one_smul]
        simp_rw [smul_sub, smul_add, smul_smul]
        ring_nf at hqeq hqeq' ⊢
        rw [hqeq, hqeq', hlin]
        module
      rcases smul_eq_zero.mp hz with hs | hs
      · exact (hone hs).elim
      · exact sub_eq_zero.mp hs
    have hqzero : q = 0 := by
      apply hT 1 (by simp) q ⟨le_of_lt hqpos, hqle⟩
      rw [htri]
      exact verts_lie_in_link L A hA
    linarith
  · have hone : 1 - u ≠ 0 := by linarith [hu.2]
    have hscaled : (1 - u) • (A - L.next A) = 0 := by
      rw [← sub_eq_zero] at h
      rw [← h]
      rw [← hsum]
      module
    have : A = L.next A := by
      rcases smul_eq_zero.mp hscaled with hs | hs
      · exact (hone hs).elim
      · exact sub_eq_zero.mp hs
    exact hAne this
  · let q : ℝ := (u + v - 1) / v
    have hvpos : 0 < v := by linarith [hu.2]
    have hqpos : 0 < q := by
      dsimp [q]
      exact div_pos (by linarith) hvpos
    have hqle : q ≤ 1 := by
      dsimp [q]
      apply (div_le_one hvpos).2
      linarith [hu.2]
    have hqeq : v * q = u + v - 1 := by
      dsimp [q]
      field_simp [ne_of_gt hvpos]
    have htri : L⟨A, 0; C, q⟩ = L.next A := by
      have hvne : v ≠ 0 := ne_of_gt hvpos
      have hlin : v • L.next A = (1 - u) • A + (u + v - 1) • C := by
        calc
          _ = ((1 - v) • C + v • L.next A) - (1 - v) • C := by module
          _ = ((1 - u) • A + u • C) - (1 - v) • C := by rw [← h]
          _ = _ := by module
      have hqeq' : v * (1 - q) = 1 - u := by linarith [hqeq]
      have hz : v • (L⟨A, 0; C, q⟩ - L.next A) = 0 := by
        dsimp [Link.TriFunc, LinkFunction]
        simp only [zero_smul]
        simp_rw [smul_sub, smul_add, smul_smul]
        ring_nf at hqeq hqeq' ⊢
        rw [hqeq', hqeq, hlin]
        module
      rcases smul_eq_zero.mp hz with hs | hs
      · exact (hvne hs).elim
      · exact sub_eq_zero.mp hs
    have hqzero : q = 0 := by
      apply hT 0 (by simp) q ⟨le_of_lt hqpos, hqle⟩
      rw [htri]
      exact verts_lie_in_link L (L.next A) hnext
    linarith

/--
(2) Suppose C is a point in space that does not lie on K. If the
triangle ABC, formed by AB and C, does not intersect K, with
the exception of the edge AB, then we may remove AB and
add the two edges AC and CB.
-/
def AddAt [DecidableEq E] (L : PLLink E) (A : E) (hA : A ∈ L.V)
  (C : E) (hT : NonIntersectingTriangle L A C) : PLLink E :=
  {
    next := Equiv.trans (Equiv.swap A C) L.next
    V := insert C L.V
    fix := by
      intro p
      aesop
      · apply non_inter_tri_not_in at hT
        have nhT : LiesInLink (L.next A) L := by
          apply verts_lie_in_link
          apply Link.next_closed
          exact hA
        contradiction
        exact hA
      · apply non_inter_tri_not_in at hT
        have nh : LiesInLink C L := by
          apply verts_lie_in_link
          apply Link.if_next_vert_then_vert
          exact hA
        contradiction
        exact hA
      · apply non_inter_tri_not_in at hT
        have nhT : LiesInLink (L.next A) L := by
          apply verts_lie_in_link
          exact h_1
        contradiction
        exact hA
      · apply (L.fix p).mp at h_1
        contradiction
      · apply (L.fix p).mpr at a
        exact a
    injection := by
      intro P hP Q hQ u v huv h
      have hCnot : C ∉ L.V := non_inter_tri_not_vert L A hA C hT
      have hCneA : C ≠ A := by
        intro hCA
        apply hCnot
        simpa [hCA] using hA
      have hnextC : L.next C = C := Link.not_vertex_is_fix L.toPrePLLink C hCnot
      have hPV : P = C ∨ P ∈ L.V := Finset.mem_insert.mp hP
      have hQV : Q = C ∨ Q ∈ L.V := Finset.mem_insert.mp hQ
      rcases huv with ⟨hu, hv⟩
      by_cases hPA : P = A
      · subst P
        by_cases hQA : Q = A
        · subst Q
          refine ⟨rfl, NIT.addAt_ac_inj L A C hA hT ?_⟩
          simpa [LinkFunction, hnextC] using h
        · rcases hQV with hQC | hQV
          · subst Q
            exfalso
            apply NIT.addAt_ac_ne_cb L A C hA hT hu hv
            simpa [LinkFunction, hnextC, hCneA] using h
          · have hQneC : Q ≠ C := by
              intro hQC
              apply hCnot
              simpa [hQC] using hQV
            have hac := NIT.addAt_ac_eq_old L A C Q hA hQV hT hu hv
                (by simpa [LinkFunction, hnextC, hCneA, hQA, hQneC, Equiv.swap_apply_of_ne_of_ne] using h)
            exact (hQA hac.1.symm).elim
      · rcases hPV with hPC | hPV
        · subst P
          by_cases hQA : Q = A
          · subst Q
            exfalso
            apply NIT.addAt_ac_ne_cb L A C hA hT hv hu
            simpa [LinkFunction, hnextC, hCneA] using h.symm
          · rcases hQV with hQC | hQV
            · subst Q
              refine ⟨rfl, NIT.addAt_cb_inj L A C hA hT ?_⟩
              simpa [LinkFunction, hnextC, hCneA] using h
            · have hQneC : Q ≠ C := by
                intro hQC
                apply hCnot
                simpa [hQC] using hQV
              exfalso
              apply NIT.addAt_cb_ne_old L A C Q hQV hT hu hv
              simpa [LinkFunction, hnextC, hCneA, hQA, hQneC,
                Equiv.swap_apply_of_ne_of_ne] using h
        · by_cases hQA : Q = A
          · subst Q
            have hPneC : P ≠ C := by
              intro hPC
              apply hCnot
              simpa [hPC] using hPV
            have hac := NIT.addAt_ac_eq_old L A C P hA hPV hT hv hu
                (by simpa [LinkFunction, hnextC, hCneA, hPA, hPneC, Equiv.swap_apply_of_ne_of_ne] using h.symm)
            exact (hPA hac.1.symm).elim
          · rcases hQV with hQC | hQV
            · subst Q
              have hPneC : P ≠ C := by
                intro hPC
                apply hCnot
                simpa [hPC] using hPV
              exfalso
              apply NIT.addAt_cb_ne_old L A C P hPV hT hv hu
              simpa [LinkFunction, hnextC, hCneA, hPA, hPneC,
                Equiv.swap_apply_of_ne_of_ne] using h.symm
            · have hPneC : P ≠ C := by
                intro hPC
                apply hCnot
                simpa [hPC] using hPV
              have hQneC : Q ≠ C := by
                intro hQC
                apply hCnot
                simpa [hQC] using hQV
              have hold : LinkFunction L (P, u) = LinkFunction L (Q, v) := by
                simpa [LinkFunction, hnextC, hCneA, hPA, hQA, hPneC, hQneC,
                  Equiv.swap_apply_of_ne_of_ne] using h
              exact L.injection P hPV Q hQV u v ⟨hu, hv⟩ hold
  }

end KnotTheory
