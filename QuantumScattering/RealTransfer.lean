/- F1 candidate. Real state propagation, independent of potential shape. -/
import QuantumScattering.State

noncomputable section
namespace QuantumScattering

/-- A real two-dimensional transfer map with unit determinant. Concrete layer
constructors PROVE the last field; a user never supplies scattering unitarity. -/
@[ext] structure RealTransfer where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  unitDet : a*d-b*c=1

namespace RealTransfer

def identity : RealTransfer := ⟨1,0,0,1,by norm_num⟩

def act (P : RealTransfer) (y : State) : State :=
  ⟨(P.a : ℂ)*y.value + (P.b : ℂ)*y.slope,
   (P.c : ℂ)*y.value + (P.d : ℂ)*y.slope⟩

/-- `Q.after P` traverses P FIRST, Q SECOND, so its matrix is Q*P. -/
def after (Q P : RealTransfer) : RealTransfer where
  a := Q.a*P.a+Q.b*P.c
  b := Q.a*P.b+Q.b*P.d
  c := Q.c*P.a+Q.d*P.c
  d := Q.c*P.b+Q.d*P.d
  unitDet := by
    calc
      _ = (Q.a*Q.d-Q.b*Q.c)*(P.a*P.d-P.b*P.c) := by ring
      _ = 1 := by rw [Q.unitDet,P.unitDet]; norm_num

def reverse (P : RealTransfer) : RealTransfer :=
  ⟨P.d,-P.b,-P.c,P.a,by nlinarith [P.unitDet]⟩

def matrix (P : RealTransfer) : Matrix (Fin 2) (Fin 2) ℝ := !![P.a,P.b;P.c,P.d]

lemma matrix_det (P : RealTransfer) : P.matrix.det=1 := by
  simpa [matrix,Matrix.det_fin_two] using P.unitDet

@[simp] lemma identity_act (y : State) : identity.act y = y := by
  ext <;> simp [identity,act]

lemma after_act (Q P : RealTransfer) (y : State) :
    (Q.after P).act y = Q.act (P.act y) := by
  ext <;> simp [after,act] <;> ring

lemma after_assoc (R Q P : RealTransfer) :
    R.after (Q.after P) = (R.after Q).after P := by
  ext <;> simp [after] <;> ring

@[simp] lemma identity_after (P : RealTransfer) : identity.after P = P := by
  ext <;> simp [identity,after]
@[simp] lemma after_identity (P : RealTransfer) : P.after identity = P := by
  ext <;> simp [identity,after]

lemma reverse_after (P : RealTransfer) : P.reverse.after P = identity := by
  ext <;> simp [reverse,after,identity] <;> nlinarith [P.unitDet]

lemma after_reverse (P : RealTransfer) : P.after P.reverse = identity := by
  ext <;> simp [reverse,after,identity] <;> nlinarith [P.unitDet]

lemma act_injective (P : RealTransfer) : Function.Injective P.act := by
  intro y z h
  have hh := congrArg P.reverse.act h
  simpa only [← after_act,reverse_after,identity_act] using hh

/-- Symplectic/flux identity obtained by direct real algebra. -/
theorem flux_preserved (P : RealTransfer) (y : State) : (P.act y).flux=y.flux := by
  calc
    (P.act y).flux = (P.a*P.d-P.b*P.c)*y.flux := by
      simp [act,State.flux,fluxForm,Complex.mul_re,Complex.mul_im] <;> ring
    _ = y.flux := by rw [P.unitDet,one_mul]

/-- Arbitrarily long ordered finite compositions, not fixed-size examples. -/
def chain : List RealTransfer → RealTransfer
  | [] => identity
  | P::rest => (chain rest).after P

lemma chain_append (xs ys : List RealTransfer) :
    chain (xs++ys) = (chain ys).after (chain xs) := by
  induction xs with
  | nil => simp [chain]
  | cons p rest ih => simp [chain,ih,after_assoc]

theorem chain_flux (xs : List RealTransfer) (y : State) :
    ((chain xs).act y).flux=y.flux := (chain xs).flux_preserved y

end RealTransfer
end QuantumScattering
