module

public import DynaLean.Defs
public import DynaLean.EulerScheme
public import DynaLean.EulerBound

@[expose] public section

namespace ODE

structure DigitalTwin {k : ℕ} (z : ℝ → ℝ^k)
  (f g : ℝ → (ℝ^k) → ℝ^k) (Ω : Set (ℝ × ℝ^k))
  (εz : ℚ) (t₀ T : ℚ) where
  z₀ : ℝ^k
  hz : SolutionExistsVector g z₀ z (t₀ : ℝ) T (Set.Icc (t₀ : ℝ) T)
  hzΩ : ∀ t ∈ Set.Icc (t₀ : ℝ) T, (t, z t) ∈ Ω
  hfg : ∀ t ∈ Set.Icc (t₀ : ℝ) T, ∀ x : ℝ^k, (t, x) ∈ Ω →
          ‖f t x - g t (z t)‖ ≤ (εz : ℝ)

section MemBox

def MemBox {k : ℕ} (x : ℝ^k) (A B : Fin k → Option ℚ) : Prop :=
  ∀ i : Fin k,
  match A i, B i with
  | some a, some b => (a ≤ x i) ∧ (x i ≤ b)
  | some a, none => a ≤ x i
  | none, some b => x i ≤ b
  | none, none => True

structure Schedule (k : ℕ) (t₀ T : ℚ) where
  p : ℕ
  hp : p ≠ 0
  τ  : Fin (p+1) → ℚ
  hmono  : StrictMono τ
  hfirst : τ 0 = t₀
  hlast  : τ (Fin.last p) = T
  A : Fin (p + 1) → Fin k → Option ℚ
  B : Fin (p + 1) → Fin k → Option ℚ
  N : Fin p → ℕ
  hN : ∀ i, N i ≠ 0

namespace Schedule
variable {k : ℕ} {t₀ T : ℚ} (sch : Schedule k t₀ T)

def h (i : Fin sch.p) : ℚ := sch.τ (i.succ) - sch.τ i.castSucc

def δ (i : Fin sch.p) : ℚ := sch.h i / (sch.N i : ℚ)

def s (i : Fin sch.p) (n : ℕ) : ℚ := sch.τ i.castSucc + n * sch.δ i

theorem h_pos (i : Fin sch.p) : 0 < sch.h i := sub_pos.mpr (sch.hmono (Fin.castSucc_lt_succ))

theorem δ_pos (i : Fin sch.p) : 0 < sch.δ i := by
  simp only [δ, sch.h_pos i, div_pos_iff_of_pos_left, Nat.cast_pos]
  apply Nat.pos_of_ne_zero (sch.hN i)

theorem s_zero (i : Fin sch.p) : sch.s i 0 = sch.τ i.castSucc := by
  simp only [s, CharP.cast_eq_zero, zero_mul, add_zero]

theorem s_last (i : Fin sch.p) : sch.s i (sch.N i) = sch.τ (i.succ) := by
  simp only [s, δ]
  rw [IsUnit.mul_div_cancel _ (sch.h i)]
  · simp only [h, add_sub_cancel]
  · simp only [isUnit_iff_ne_zero, ne_eq, Nat.cast_eq_zero]
    exact (sch.hN i)
end Schedule

def MeasuredBy {k : ℕ} {t₀ T : ℚ} (z : ℝ → ℝ^k) (sch : Schedule k t₀ T) : Prop :=
  ∀ i : Fin (sch.p + 1), MemBox (z (sch.τ i)) (sch.A i) (sch.B i)

def sqrtUB (x : ℚ) : ℚ := (Nat.sqrt (x.num.toNat * x.den) + 1) / x.den

def qnormUB {k : ℕ} (x : ℚ^k) : ℚ := sqrtUB (∑ i : Fin k, (x i) ^ 2)

def ObtainLU {k : ℕ} (c : ℚ^k) (r : ℚ) (A B : Fin k → Option ℚ) : List (ℚ × ℚ) :=
  List.ofFn fun i : Fin k =>
    ( match A i with | some a => max a (c.ofLp i - r) | none => c.ofLp i - r,
      match B i with | some b => min b (c.ofLp i + r) | none => c.ofLp i + r )

def Rec {k : ℕ} (c : ℚ^k) (r : ℚ) (A B : Fin k → (Option ℚ)) : Option ((ℚ^k) × ℚ) :=
  let LU := ObtainLU c r A B
  if LU.all (fun (l, u) => l ≤ u) then
    let rbox := sqrtUB ((LU.map (fun (l, u) => ((u - l) / 2) ^ 2)).sum)
    if rbox ≤ r then
      some ((WithLp.equiv 2 (Fin k → ℚ)).symm (fun i => (LU[i]!.1 + LU[i]!.2) / 2), rbox)
    else
      some (c, r)
  else
    none

def EB (K ε M δ : ℚ) (n : ℕ) := (ε + M*δ/2) * ((1 + K*δ)^n - 1) / K

abbrev Node (k : ℕ) := (ℚ^k) × ℚ

def segEnd {k : ℕ} {t₀ T : ℚ} (sch : Schedule k t₀ T) (m : ℚ → (ℚ^k) → ℚ^k)
    (εz εm K M : ℚ) (i : Fin sch.p) (c : ℚ^k) (r : ℚ) : Node k :=
  let S := LastVectorSchema (sch.τ i.castSucc) (sch.τ (i.succ)) c m (sch.N i) (sch.hN i)
    (sch.hmono (Fin.castSucc_lt_succ))
  (S.x (sch.N i), r + εz * (sch.h i) + EB K εm M (sch.δ i) (sch.N i))

def nodeAt {k : ℕ} {t₀ T : ℚ} (sch : Schedule k t₀ T) (m : ℚ → (ℚ^k) → ℚ^k)
    (x₀ : ℚ^k) (ρ₀ εz εm K M : ℚ) : Fin (sch.p + 1) → Option (Node k) :=
  Fin.induction (motive := fun _ => Option (Node k))
    (Rec x₀ ρ₀ (sch.A 0) (sch.B 0))
    (fun i prev => do
      let (c, ρ) ← prev
      let (cE, rE) := segEnd sch m εz εm K M i c ρ
      Rec cE rE (sch.A i.succ) (sch.B i.succ))

def BuildTube {k : ℕ} {t₀ T : ℚ} (sch : Schedule k t₀ T) (m : ℚ → (ℚ^k) → ℚ^k)
    (x₀ : ℚ^k) (ρ₀ εz εm K M : ℚ) : Option (Node k) :=
  nodeAt sch m x₀ ρ₀ εz εm K M (Fin.last sch.p)

def driftIndex {k : ℕ} {t₀ T : ℚ} (sch : Schedule k t₀ T) (m : ℚ → (ℚ^k) → ℚ^k)
    (x₀ : ℚ^k) (ρ₀ εz εm K M : ℚ) : Option (Fin (sch.p + 1)) :=
  (List.finRange (sch.p + 1)).find? fun i => (nodeAt sch m x₀ ρ₀ εz εm K M i).isNone

noncomputable def segCentre {k : ℕ} {t₀ T : ℚ} (sch : Schedule k t₀ T)
    (m : ℚ → (ℚ^k) → ℚ^k) (i : Fin sch.p) (c : ℚ^k) (t : ℝ) : ℝ^k :=
  (LastVectorSchema (sch.τ i.castSucc) (sch.τ i.succ) c m (sch.N i) (sch.hN i)
     (sch.hmono (Fin.castSucc_lt_succ))).plR t

noncomputable def segRadius {k : ℕ} {t₀ T : ℚ} (sch : Schedule k t₀ T)
    (εz εm K M : ℚ) (i : Fin sch.p) (ρ : ℚ) (t : ℝ) : ℝ :=
  (ρ : ℝ) + (εz : ℝ) * (t - (sch.τ i.castSucc : ℝ)) + (EB K εm M (sch.δ i) (sch.N i) : ℝ)

structure SegmentCert {k : ℕ} {t₀ T : ℚ} (sch : Schedule k t₀ T)
    (f : ℝ → (ℝ^k) → ℝ^k) (m : ℚ → (ℚ^k) → ℚ^k) (Ω : Set (ℝ × ℝ^k))
    (εm K M : ℚ) (i : Fin sch.p) (c : ℚ^k) where
  y : ℝ → ℝ^k
  hy : SolutionExistsVector f (c : ℝ^k) y (sch.τ i.castSucc : ℝ) (sch.τ i.succ : ℝ)
        (Set.Icc (sch.τ i.castSucc : ℝ) (sch.τ i.succ : ℝ))
  hyΩ : ∀ s ∈ Set.Icc (sch.τ i.castSucc : ℝ) (sch.τ i.succ : ℝ), (s, y s) ∈ Ω
  hEB : ∀ t ∈ Set.Icc (sch.τ i.castSucc : ℝ) (sch.τ i.succ : ℝ),
           (let S := LastVectorSchema (sch.τ i.castSucc) (sch.τ i.succ) c m (sch.N i) (sch.hN i)
                       (sch.hmono (Fin.castSucc_lt_succ))
            ‖y t - S.plR t‖ ≤ (EB K εm M (sch.δ i) (sch.N i) : ℝ))

end MemBox

end ODE
