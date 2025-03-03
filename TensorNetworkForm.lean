-- This module serves as the root of the `TensorNetworkForm` library.
-- Import modules here that should be built as part of the library.
import TensorNetworkForm.Basic

import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Exponential

open BigOperators Finset
open Matrix

def sqrt2_approx : ℚ := 14142135623730950488 / 10^19

-- A MPS tensor with physical dimension d and bond dimension χ.
structure MPS_tensor (α : Type) (d χ : ℕ) where
  data : Fin d → Matrix (Fin χ) (Fin χ) α

-- A Finite MPS with open boundary conditions and constant bond dimension.
structure Finite_MPS (α : Type) [Ring α] [StarRing α] (N d χ: ℕ) where
  tensors : Fin N → MPS_tensor α d χ  -- N MPS tensors
  boundary_left : Matrix (Fin 1) (Fin χ) α  -- Left boundary vector (optional)
  boundary_right : Matrix (Fin χ) (Fin 1) α -- Right boundary vector (optional)
  hN : 0 < N
  hd : 0 < d
  hχ : 0 < χ

def contract_mps_tensors {α : Type} [Ring α] [StarRing α] {N d χ : ℕ}
  (mps : Finite_MPS α N d χ) (t : Fin N → Fin d) (n : Fin N): Matrix (Fin χ) (Fin χ) α :=
  match n with
  | ⟨0, h0⟩ => (mps.tensors ⟨0, h0⟩).data (t ⟨0, h0⟩)
  | ⟨i+1, hi⟩ => (contract_mps_tensors mps t ⟨i, Nat.lt_of_succ_lt hi⟩) * (mps.tensors ⟨i+1,hi⟩).data (t ⟨i+1, hi⟩)

def get_component {α : Type} [Ring α] [StarRing α] {N d χ : ℕ}
  (mps : Finite_MPS α N d χ) (t : Fin N → Fin d) : α :=
  (mps.boundary_left * (contract_mps_tensors mps t ⟨N-1, Nat.pred_lt (Nat.ne_of_gt mps.hN)⟩) * mps.boundary_right) 0 0

-- Create a Finset of all possible functions from fin N to fin d

def norm_mps {α : Type} [Ring α] [StarRing α] {N d χ : ℕ} (mps : Finite_MPS α N d χ) : α :=
  let all_functions : Finset (Fin N → Fin d) :=  Finset.univ
  ∑ f ∈ all_functions,  (get_component mps f) * star (get_component mps f)

def aklt_tensor : MPS_tensor ℝ 3 2 :=
{ data := fun
    | ⟨0, _⟩ => Matrix.of ![![0, sqrt2_approx], ![0, 0]]  -- S^z = -1
    | ⟨1, _⟩ => Matrix.of ![![-1, 0], ![0, 1]]           -- S^z =  0
    | ⟨2, _⟩ => Matrix.of ![![0, 0], ![sqrt2_approx, 0]]  -- S^z = +1
}

-- Define left and right boundary vectors
def boundary_left : Matrix (Fin 1) (Fin 2) ℝ :=
  Matrix.of ![![1, 0]]  -- Row vector (1 × χ)

def boundary_right : Matrix (Fin 2) (Fin 1) ℝ :=
  Matrix.of ![![0], ![1]]  -- Column vector (χ × 1)

-- Define the N-site AKLT MPS
def AKLT_MPS (N : {n : ℕ // 0 < n}) : Finite_MPS ℝ N.val 3 2 :=
{ tensors := fun _ => aklt_tensor,  -- Same tensor at every site
  boundary_left := boundary_left,
  boundary_right := boundary_right,
  hN := N.property,
  hd := by decide,
  hχ := by decide
}

def component_index : Fin 2 → Fin 3 :=
  fun
  | ⟨0,_⟩  => ⟨1, by decide⟩
  | ⟨1,_⟩  => ⟨0, by decide⟩


#eval get_component (AKLT_MPS ⟨2, by decide⟩) component_index
#eval norm_mps (AKLT_MPS ⟨2, by decide⟩)

def exist_phase {α : Type} [Ring α] [StarRing α] {N d χ : ℕ} (Amps Bmps : Finite_MPS α N d χ) : Prop := ∃ t : α, ∀ (x : (Fin N → Fin d)), (t * star t = 1) ∧ (get_component Amps x) = t * (get_component Bmps x)
axiom eq_MPS {α : Type} [Ring α] [StarRing α] {N d χ : ℕ} (Amps Bmps : Finite_MPS α N d χ) : Amps = Bmps ↔ exist_phase Amps Bmps
