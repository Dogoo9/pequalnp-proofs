import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3795_aux
open PEqualNP.CircuitLowerBounds

theorem fold_prefix (L : List Gate) : ∀ d : List ℕ,
    ∃ t, L.foldl (fun d g => d ++ [g.lineDegree d]) d = d ++ t := by
  induction L with
  | nil => intro d; exact ⟨[], by simp⟩
  | cons g L ih =>
    intro d
    obtain ⟨t, ht⟩ := ih (d ++ [g.lineDegree d])
    exact ⟨[g.lineDegree d] ++ t, by simp [List.foldl_cons, ht]⟩

theorem deg_le (g : Gate) (d : List ℕ) (a b : ℕ) (h : g.inputs = [a, b]) :
    g.lineDegree d ≤ d.getD a 0 + d.getD b 0 := by
  unfold Gate.lineDegree
  rw [h]
  split_ifs
  · simp
  · simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    omega

theorem sum_pair (d : List ℕ) (n a b : ℕ) (ha : a < n) (hb : b < n) (_hab : a ≠ b) :
    (∑ w ∈ Finset.range n, d.getD w 0 * [a, b].count w) = d.getD a 0 + d.getD b 0 := by
  have : ∀ w, [a, b].count w = (if a = w then 1 else 0) + (if b = w then 1 else 0) := by
    intro w
    simp only [List.count_cons, List.count_nil, beq_iff_eq]
    omega
  simp only [this, mul_add, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.mem_range, ha, hb, ite_true]

theorem key (L : List Gate) : ∀ (d : List ℕ) (o : ℕ),
    (∀ (i : ℕ) (g : Gate), L[i]? = some g →
      ∃ a b, g.inputs = [a, b] ∧ a ≠ b ∧ a < d.length + i ∧ b < d.length + i) →
    (∀ w, d.length ≤ w → (o :: L.flatMap Gate.inputs).count w ≤ 1) →
    (∑ w ∈ Finset.range d.length, d.getD w 0 * (o :: L.flatMap Gate.inputs).count w) ≤ 1 →
    (L.foldl (fun d g => d ++ [g.lineDegree d]) d).getD o 0 ≤ 1 := by
  induction L with
  | nil =>
    intro d o _ _ hs
    simp only [List.foldl_nil]
    by_cases ho : o < d.length
    · have h1 := Finset.single_le_sum (f := fun w => d.getD w 0 * (o :: ([] : List Gate).flatMap
        Gate.inputs).count w) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr ho)
      simp only [List.flatMap_nil, List.count_singleton_self, mul_one] at h1
      simp only [List.flatMap_nil] at hs
      omega
    · rw [List.getD_eq_default _ _ (by omega)]
      omega
  | cons g L ih =>
    intro d o hg hc hs
    obtain ⟨a, b, hin, hab, ha, hb⟩ := hg 0 g rfl
    simp only [Nat.add_zero] at ha hb
    simp only [List.foldl_cons]
    set e := g.lineDegree d with he
    have hsub : (o :: L.flatMap Gate.inputs).Sublist (o :: (g :: L).flatMap Gate.inputs) := by
      simp only [List.flatMap_cons]
      exact (List.sublist_append_right _ _).cons_cons o
    apply ih (d ++ [e]) o
    · intro i g' hi
      obtain ⟨a', b', h1, h2, h3, h4⟩ := hg (i + 1) g' (by simpa using hi)
      exact ⟨a', b', h1, h2, by simp; omega, by simp; omega⟩
    · intro w hw
      exact le_trans (hsub.count_le w) (hc w (by simp at hw; omega))
    · have hlen : (d ++ [e]).length = d.length + 1 := by simp
      rw [hlen, Finset.sum_range_succ]
      have hlast : (d ++ [e]).getD d.length 0 = e := by simp
      have hpre : ∀ w ∈ Finset.range d.length, (d ++ [e]).getD w 0 = d.getD w 0 := by
        intro w hw
        rw [Finset.mem_range] at hw
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hw]
      rw [Finset.sum_congr rfl (fun w hw => by rw [hpre w hw]), hlast]
      have hcl : (o :: L.flatMap Gate.inputs).count d.length ≤ 1 :=
        le_trans (hsub.count_le _) (hc d.length le_rfl)
      have hsplit : ∀ w, (o :: (g :: L).flatMap Gate.inputs).count w =
          (o :: L.flatMap Gate.inputs).count w + [a, b].count w := by
        intro w
        simp only [List.flatMap_cons, hin, List.count_cons, List.count_append, List.count_nil]
        omega
      simp only [hsplit, mul_add, Finset.sum_add_distrib] at hs
      rw [sum_pair d d.length a b ha hb hab] at hs
      have hde := deg_le g d a b hin
      have : e * (o :: L.flatMap Gate.inputs).count d.length ≤ e := by
        calc e * _ ≤ e * 1 := Nat.mul_le_mul_left _ hcl
          _ = e := mul_one e
      omega

end PEqualNP.Outside.L_meta_3795_aux

theorem PEqualNP.Outside.L_meta_3795 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), ∀ x2 < (14 : ℕ), (∀ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x4]? = Option.some x5 → (x5.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x5.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x7 : ℕ) (x8 : ℕ), x5.inputs = [x7, x8] ∧ x7 ≠ x8 ∧ x7 < (14 : ℕ) + x4 ∧ x8 < (14 : ℕ) + x4) → (List.filter (fun (x5 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x5)) (x1.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x1.gates)).Nodup → List.count x2 (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x1.gates) ≤ (1 : ℕ) → PEqualNP.CircuitLowerBounds.HasLineDegree (14 : ℕ) {x2} x1 (1 : ℕ) := by
  intro C x2 hx2 hgates hnodup hcount
  unfold PEqualNP.CircuitLowerBounds.HasLineDegree PEqualNP.CircuitLowerBounds.Circuit.lineDeg
    PEqualNP.CircuitLowerBounds.Circuit.lineDegrees
  set init : List ℕ := (List.range 14).map fun i => if i ∈ ({x2} : Finset ℕ) then 1 else 0 with hinit
  have hlen : init.length = 14 := by simp [hinit]
  have hget : ∀ w < 14, init.getD w 0 = if w = x2 then 1 else 0 := by
    intro w hw
    simp [hinit, List.getD_eq_getElem?_getD, hw]
  by_cases ho : C.output < 14
  · obtain ⟨t, ht⟩ := PEqualNP.Outside.L_meta_3795_aux.fold_prefix C.gates init
    rw [ht, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
      ← List.getD_eq_getElem?_getD, hget _ ho]
    split_ifs <;> omega
  · apply PEqualNP.Outside.L_meta_3795_aux.key C.gates init C.output
    · intro i g hi
      obtain ⟨_, a, b, h1, h2, h3, h4⟩ := hgates i g hi
      exact ⟨a, b, h1, h2, by omega, by omega⟩
    · intro w hw
      rw [hlen] at hw
      have hc := List.nodup_iff_count_le_one.mp hnodup w
      rwa [List.count_filter (by simpa using hw)] at hc
    · rw [hlen, Finset.sum_congr rfl (fun w hw => by rw [hget w (Finset.mem_range.mp hw)])]
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_range, hx2, ite_true]
      simp only [List.count_cons, beq_iff_eq]
      have : C.output ≠ x2 := by omega
      simp [this, hcount]
