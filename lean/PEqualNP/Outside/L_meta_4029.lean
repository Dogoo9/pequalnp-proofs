import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4029_aux
open PEqualNP.CircuitLowerBounds

theorem fold_len (L : List Gate) : ∀ w : List Bool,
    (L.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length =
      w.length + L.length := by
  induction L with
  | nil => intro w; simp
  | cons g L ih => intro w; rw [List.foldl_cons, ih]; simp; omega

theorem fold_pre (L : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (L.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false =
      w.getD i false := by
  induction L with
  | nil => intro w i _; rfl
  | cons g L ih =>
    intro w i hi
    rw [List.foldl_cons, ih _ _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

def extra (o w n : ℕ) : List Gate :=
  [⟨GateOp.or, [o, 14]⟩, ⟨GateOp.or, [w, 4]⟩, ⟨GateOp.or, [26 + n + 1, 10]⟩,
    ⟨GateOp.or, [o, 26 + n + 2]⟩, ⟨GateOp.and, [26 + n, 26 + n + 3]⟩]

theorem wires_ext (C : Circuit) (L : List Gate) (o : ℕ) (y : List Bool) :
    Circuit.wires ⟨C.gates ++ L, o⟩ y =
      L.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (C.wires y) := by
  unfold Circuit.wires
  rw [List.foldl_append]

end PEqualNP.Outside.L_meta_4029_aux

theorem PEqualNP.Outside.L_meta_4029 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ),   (26 : ℕ) ≤ x1.output →     x1.output < (26 : ℕ) + x1.size →       (26 : ℕ) ≤ x2 →         x2 < (26 : ℕ) + x1.size →           (∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x7]? = Option.some x8 → (x8.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x8.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x10 : ℕ) (x11 : ℕ), x8.inputs = [x10, x11] ∧ x10 ≠ x11 ∧ x10 < (26 : ℕ) + x7 ∧ x11 < (26 : ℕ) + x7) →             (∀ (x8 : Fin (26 : ℕ) → Bool), (x1.wires (List.ofFn x8)).getD x2 Bool.false = (x8 (1 : Fin (26 : ℕ)) || x8 (2 : Fin (26 : ℕ)))) →               ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : ℕ) (x11 : ℕ) (x12 : ℕ),                 x9.size ≤ x1.size + (5 : ℕ) ∧                   (∀ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate), x9.gates[x13]? = Option.some x14 → (x14.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x14.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x16 : ℕ) (x17 : ℕ), x14.inputs = [x16, x17] ∧ x16 ≠ x17 ∧ x16 < (26 : ℕ) + x13 ∧ x17 < (26 : ℕ) + x13) ∧                     x9.output = (26 : ℕ) + x10 ∧                       x9.gates[x10]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x11, x12] : PEqualNP.CircuitLowerBounds.Gate } ∧                         ∀ (x13 : Fin (26 : ℕ) → Bool),                           have x14 : List Bool := x9.wires (List.ofFn x13);                           have x15 : Bool := x1.eval (List.ofFn x13);                           x14.getD x11 Bool.false = (x15 || x13 (14 : Fin (26 : ℕ))) ∧ x14.getD x12 Bool.false = (x15 || x13 (1 : Fin (26 : ℕ)) || x13 (2 : Fin (26 : ℕ)) || x13 (4 : Fin (26 : ℕ)) || x13 (10 : Fin (26 : ℕ))) ∧ x9.eval (List.ofFn x13) = (x14.getD x11 Bool.false && x14.getD x12 Bool.false) := by
  intro C w ho1 ho2 hw1 hw2 hg hval
  have hsz : C.size = C.gates.length := rfl
  refine ⟨⟨C.gates ++ PEqualNP.Outside.L_meta_4029_aux.extra C.output w C.size, 26 + (C.size + 4)⟩,
    C.size + 4, 26 + C.size, 26 + C.size + 3, ?_, ?_, rfl, ?_, ?_⟩
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, PEqualNP.Outside.L_meta_4029_aux.extra]
  · intro j g hj
    rcases lt_or_ge j C.gates.length with h | h
    · rw [List.getElem?_append_left h] at hj
      exact hg j g hj
    · rw [List.getElem?_append_right h] at hj
      obtain ⟨k, rfl⟩ : ∃ k, j = C.gates.length + k := ⟨j - C.gates.length, by omega⟩
      rw [Nat.add_sub_cancel_left] at hj
      rcases k with _ | _ | _ | _ | _ | k <;> simp [PEqualNP.Outside.L_meta_4029_aux.extra] at hj <;> subst hj <;> simp <;> omega
  · simp [hsz, PEqualNP.Outside.L_meta_4029_aux.extra]
  · intro x
    dsimp only
    have hlen : (C.wires (List.ofFn x)).length = 26 + C.size := by
      unfold PEqualNP.CircuitLowerBounds.Circuit.wires
      rw [PEqualNP.Outside.L_meta_4029_aux.fold_len]; simp [hsz]
    have hin : ∀ i : ℕ, (hi : i < 26) → (C.wires (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
      intro i hi
      unfold PEqualNP.CircuitLowerBounds.Circuit.wires
      rw [PEqualNP.Outside.L_meta_4029_aux.fold_pre _ _ _ (by simp; omega),
        List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp [hi]
    have hw := hval x
    have hev : C.eval (List.ofFn x) = (C.wires (List.ofFn x)).getD C.output false := rfl
    rw [hev]
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval
    rw [PEqualNP.Outside.L_meta_4029_aux.wires_ext]
    simp only [PEqualNP.Outside.L_meta_4029_aux.extra]
    generalize hW : C.wires (List.ofFn x) = W at hlen hin hw ⊢
    have e14 := hin 14 (by omega)
    have e4 := hin 4 (by omega)
    have e10 := hin 10 (by omega)
    simp only [List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil,
      PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_cons, List.any_nil, List.all_cons,
      List.all_nil, id, Bool.or_false, Bool.and_true, List.getD_eq_getElem?_getD,
      List.getElem?_append, List.length_append, List.length_cons, List.length_nil, hlen] at e14 e4 e10 hw ⊢
    have b14 : 14 < 26 + C.size := by omega
    have b4 : 4 < 26 + C.size := by omega
    have b10 : 10 < 26 + C.size := by omega
    have o25 : C.output ≤ C.size + 25 := by omega
    have o26 : C.output ≤ C.size + 26 := by omega
    have o27 : C.output ≤ C.size + 27 := by omega
    have w25 : w ≤ C.size + 25 := by omega
    simp +arith [e14, e4, e10, Bool.or_assoc, o25, o26, o27, w25]
    simp [hw, Bool.or_assoc]
