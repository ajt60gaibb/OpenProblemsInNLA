import Mathlib

open scoped BigOperators

namespace IV02

structure PartitionData where
  m : ℕ
  hm : 0 < m
  w : Fin m → ℚ
  hw : ∀ i, 0 < w i
  W : ℚ
  hW : 0 < W
  hWsum : W = ∑ i, w i

def t (P : PartitionData) (i : Fin P.m) : ℚ := P.w i / (10 * P.W ^ 2)

def c (P : PartitionData) (i : Fin P.m) : ℚ :=
  (1 - t P i ^ 2) / (1 + t P i ^ 2)

def s (P : PartitionData) (i : Fin P.m) : ℚ :=
  (2 * t P i) / (1 + t P i ^ 2)

lemma denominator_pos (P : PartitionData) (i : Fin P.m) :
    0 < 1 + t P i ^ 2 := by
  positivity

lemma rotation_identity (P : PartitionData) (i : Fin P.m) :
    c P i ^ 2 + s P i ^ 2 = 1 := by
  have h := ne_of_gt (denominator_pos P i)
  dsimp [c, s]
  field_simp [h]
  ring

def layerCount (P : PartitionData) : ℕ := 4 * P.m - 2

lemma layerCount_even (P : PartitionData) : Even (layerCount P) := by
  cases h : P.m with
  | zero =>
    have hm : 0 < 0 := h ▸ P.hm
    omega
  | succ m =>
    refine ⟨2 * m + 1, ?_⟩
    norm_num [layerCount, h]
    omega

lemma layerCount_pos (P : PartitionData) : 0 < layerCount P := by
  cases h : P.m with
  | zero =>
    have hm : 0 < 0 := h ▸ P.hm
    omega
  | succ m =>
    norm_num [layerCount, h]
    omega

end IV02
