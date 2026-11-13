/- F1 candidate. Flux-normalized channels for unequal exterior wave numbers.
The normalization is essential: raw wave amplitudes do not have a Euclidean
unitary S matrix when k_left and k_right differ. Constant mass is retained. -/
import QuantumScattering.Layers

noncomputable section
namespace QuantumScattering

namespace RealTransfer

def scale (u : ℝ) (hu : u ≠ 0) : RealTransfer :=
  ⟨u,0,0,u⁻¹,by simp [hu]⟩
end RealTransfer

@[ext] structure Modes where
  forward : ℂ
  backward : ℂ

def Modes.flux (x : Modes) : ℝ := absSq x.forward-absSq x.backward

def encodeCanonical (x : Modes) : State :=
  ⟨x.forward+x.backward,Complex.I*(x.forward-x.backward)⟩

def decodeCanonical (y : State) : Modes :=
  ⟨(y.value-Complex.I*y.slope)/2,(y.value+Complex.I*y.slope)/2⟩

@[simp] lemma decode_encode (x : Modes) : decodeCanonical (encodeCanonical x)=x := by
  ext <;> apply Complex.ext <;>
    simp [decodeCanonical,encodeCanonical,Complex.mul_re,Complex.mul_im] <;> ring

@[simp] lemma encode_decode (y : State) : encodeCanonical (decodeCanonical y)=y := by
  ext <;> apply Complex.ext <;>
    simp [decodeCanonical,encodeCanonical,Complex.mul_re,Complex.mul_im] <;> ring

lemma encodeCanonical_injective : Function.Injective encodeCanonical := by
  intro x y h
  simpa using congrArg decodeCanonical h

lemma encodeCanonical_flux (x : Modes) : (encodeCanonical x).flux=x.flux := by
  simp [encodeCanonical,State.flux,Modes.flux,fluxForm,absSq,
    Complex.mul_re,Complex.mul_im] <;> ring

/-- An open asymptotic propagation channel. Interior thresholds remain allowed;
exterior k=0 or closed channels need a different asymptotic scattering space. -/
structure Port where
  k : ℝ
  positive : 0 < k

namespace Port

def root (p : Port) : ℝ := Real.sqrt p.k
lemma root_pos (p : Port) : 0 < p.root := Real.sqrt_pos.2 p.positive
lemma root_sq (p : Port) : p.root^2=p.k := Real.sq_sqrt (le_of_lt p.positive)

def normalizer (p : Port) : RealTransfer := RealTransfer.scale p.root (ne_of_gt p.root_pos)

def encode (p : Port) (x : Modes) : State := p.normalizer.reverse.act (encodeCanonical x)

def decode (p : Port) (y : State) : Modes := decodeCanonical (p.normalizer.act y)

@[simp] lemma decode_encode (p : Port) (x : Modes) : p.decode (p.encode x)=x := by
  simp only [decode,encode,← RealTransfer.after_act,RealTransfer.after_reverse,
    RealTransfer.identity_act,QuantumScattering.decode_encode]

@[simp] lemma encode_decode (p : Port) (y : State) : p.encode (p.decode y)=y := by
  simp only [decode,encode,QuantumScattering.encode_decode,← RealTransfer.after_act,
    RealTransfer.reverse_after,RealTransfer.identity_act]

lemma encode_injective (p : Port) : Function.Injective p.encode := by
  intro x y h
  simpa using congrArg p.decode h

/-- Each unit mode carries reduced current one, independently of the lead k. -/
theorem encode_flux (p : Port) (x : Modes) : (p.encode x).flux=x.flux := by
  rw [encode,RealTransfer.flux_preserved,encodeCanonical_flux]

lemma encode_value (p : Port) (x : Modes) :
    (p.encode x).value=(x.forward+x.backward)/(p.root : ℂ) := by
  simp [encode,normalizer,RealTransfer.scale,RealTransfer.reverse,
    RealTransfer.act,encodeCanonical,div_eq_mul_inv]
  ring

lemma encode_slope (p : Port) (x : Modes) :
    (p.encode x).slope=(p.root : ℂ)*Complex.I*(x.forward-x.backward) := by
  simp [encode,normalizer,RealTransfer.scale,RealTransfer.reverse,
    RealTransfer.act,encodeCanonical]
  ring

end Port

/-- Coefficient transfer in the forward spatial direction. This structure does
NOT assume mirror symmetry or a purely imaginary off-diagonal coefficient. -/
structure ChannelTransfer where
  alpha : ℂ
  beta : ℂ
  balance : absSq alpha-absSq beta=1

namespace ChannelTransfer

def fromReal (P : RealTransfer) : ChannelTransfer where
  alpha := ⟨(P.a+P.d)/2,(P.b-P.c)/2⟩
  beta := ⟨(P.a-P.d)/2,(-P.b-P.c)/2⟩
  balance := by
    change ((P.a+P.d)/2)^2+((P.b-P.c)/2)^2-
      (((P.a-P.d)/2)^2+((-P.b-P.c)/2)^2)=1
    nlinarith [P.unitDet]

def act (M : ChannelTransfer) (x : Modes) : Modes :=
  ⟨M.alpha*x.forward+M.beta*x.backward,
    star M.beta*x.forward+star M.alpha*x.backward⟩

lemma alpha_ne_zero (M : ChannelTransfer) : M.alpha ≠ 0 := by
  intro h
  have hb := M.balance
  rw [h,absSq_zero] at hb
  linarith [absSq_nonneg M.beta]

lemma star_alpha_ne_zero (M : ChannelTransfer) : star M.alpha ≠ 0 := by
  intro h
  apply M.alpha_ne_zero
  simpa using congrArg star h

lemma complex_balance (M : ChannelTransfer) :
    M.alpha*star M.alpha-M.beta*star M.beta=1 := by
  rw [mul_star_self,mul_star_self,← Complex.ofReal_sub]
  exact_mod_cast M.balance

/-- The channel structure is derived from the real transfer map, rather than
postulated independently of the differential equation representation. -/
theorem fromReal_action (P : RealTransfer) (x : Modes) :
    encodeCanonical ((fromReal P).act x)=P.act (encodeCanonical x) := by
  ext <;> apply Complex.ext <;>
    simp [encodeCanonical,act,fromReal,RealTransfer.act,
      Complex.mul_re,Complex.mul_im] <;> ring

theorem flux_preserved (M : ChannelTransfer) (x : Modes) : (M.act x).flux=x.flux := by
  calc
    (M.act x).flux=(absSq M.alpha-absSq M.beta)*x.flux := by
      simp [act,Modes.flux,absSq,Complex.mul_re,Complex.mul_im] <;> ring
    _ = x.flux := by rw [M.balance,one_mul]

end ChannelTransfer

/-- A change of normalized channel basis on each side of a real transfer. -/
def channelTransfer (left right : Port) (P : RealTransfer) : ChannelTransfer :=
  ChannelTransfer.fromReal (right.normalizer.after (P.after left.normalizer.reverse))

theorem channelTransfer_action (left right : Port) (P : RealTransfer) (x : Modes) :
    right.encode ((channelTransfer left right P).act x)=P.act (left.encode x) := by
  unfold channelTransfer Port.encode
  rw [ChannelTransfer.fromReal_action]
  simp only [RealTransfer.after_act]
  rw [← RealTransfer.after_act,RealTransfer.reverse_after,RealTransfer.identity_act]

end QuantumScattering
