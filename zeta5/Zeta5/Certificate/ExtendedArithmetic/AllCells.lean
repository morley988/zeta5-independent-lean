import Zeta5.Certificate.ExtendedArithmetic
import Zeta5.Certificate.ExtendedArithmetic.Chain

/-! # The complete certified finite middle-band chain -/

noncomputable section
namespace Zeta5.Certificate.ExtendedArithmetic
open Zeta5.Reuse.PrimePiecewise Filter
open scoped Topology

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def allCells : List (ArithmeticCell × ℚ) :=
  (((((((((((((((((((((((Block00.cells ++ Block01.cells) ++ Block02.cells) ++ Block03.cells) ++ Block04.cells) ++ Block05.cells) ++ Block06.cells) ++ Block07.cells) ++ Block08.cells) ++ Block09.cells) ++ Block10.cells) ++ Block11.cells) ++ Block12.cells) ++ Block13.cells) ++ Block14.cells) ++ Block15.cells) ++ Block16.cells) ++ Block17.cells) ++ Block18.cells) ++ Block19.cells) ++ Block20.cells) ++ Block21.cells) ++ Block22.cells) ++ Block23.cells)

theorem allCells_certificate : CappedChainCertificate (1 / 512) (9 / 20) areaUpper allCells := by
  have b0 : CappedChainCertificate (1 / 512) (5 / 2454) (254486947 / 500000000000) Block00.cells :=
    ⟨Block00.fits, Block00.endpoint, Block00.upper⟩
  have h0 := b0
  have b1 : CappedChainCertificate (5 / 2454) (2932 / 1376515) (557876601 / 1000000000000) Block01.cells :=
    ⟨Block01.fits, Block01.endpoint, Block01.upper⟩
  have h1 := h0.append b1
  have b2 : CappedChainCertificate (2932 / 1376515) (1 / 448) (153446181 / 250000000000) Block02.cells :=
    ⟨Block02.fits, Block02.endpoint, Block02.upper⟩
  have h2 := h1.append b2
  have b3 : CappedChainCertificate (1 / 448) (5 / 2134) (334453589 / 500000000000) Block03.cells :=
    ⟨Block03.fits, Block03.endpoint, Block03.upper⟩
  have h3 := h2.append b3
  have b4 : CappedChainCertificate (5 / 2134) (844 / 342225) (29711949 / 40000000000) Block04.cells :=
    ⟨Block04.fits, Block04.endpoint, Block04.upper⟩
  have h4 := h3.append b4
  have b5 : CappedChainCertificate (844 / 342225) (1 / 384) (829106009 / 1000000000000) Block05.cells :=
    ⟨Block05.fits, Block05.endpoint, Block05.upper⟩
  have h5 := h4.append b5
  have b6 : CappedChainCertificate (1 / 384) (5 / 1814) (114756557 / 125000000000) Block06.cells :=
    ⟨Block06.fits, Block06.endpoint, Block06.upper⟩
  have h6 := h5.append b6
  have b7 : CappedChainCertificate (5 / 1814) (2132 / 728035) (259405753 / 250000000000) Block07.cells :=
    ⟨Block07.fits, Block07.endpoint, Block07.upper⟩
  have h7 := h6.append b7
  have b8 : CappedChainCertificate (2132 / 728035) (1 / 320) (1181394001 / 1000000000000) Block08.cells :=
    ⟨Block08.fits, Block08.endpoint, Block08.upper⟩
  have h8 := h7.append b8
  have b9 : CappedChainCertificate (1 / 320) (5 / 1494) (1337618529 / 1000000000000) Block09.cells :=
    ⟨Block09.fits, Block09.endpoint, Block09.upper⟩
  have h9 := h8.append b9
  have b10 : CappedChainCertificate (5 / 1494) (1732 / 480595) (1550494737 / 1000000000000) Block10.cells :=
    ⟨Block10.fits, Block10.endpoint, Block10.upper⟩
  have h10 := h9.append b10
  have b11 : CappedChainCertificate (1732 / 480595) (1 / 256) (363468787 / 200000000000) Block11.cells :=
    ⟨Block11.fits, Block11.endpoint, Block11.upper⟩
  have h11 := h10.append b11
  have b12 : CappedChainCertificate (1 / 256) (5 / 1174) (2127747961 / 1000000000000) Block12.cells :=
    ⟨Block12.fits, Block12.endpoint, Block12.upper⟩
  have h12 := h11.append b12
  have b13 : CappedChainCertificate (5 / 1174) (148 / 31595) (2564743329 / 1000000000000) Block13.cells :=
    ⟨Block13.fits, Block13.endpoint, Block13.upper⟩
  have h13 := h12.append b13
  have b14 : CappedChainCertificate (148 / 31595) (1 / 192) (3149545437 / 1000000000000) Block14.cells :=
    ⟨Block14.fits, Block14.endpoint, Block14.upper⟩
  have h14 := h13.append b14
  have b15 : CappedChainCertificate (1 / 192) (5 / 854) (3899974557 / 1000000000000) Block15.cells :=
    ⟨Block15.fits, Block15.endpoint, Block15.upper⟩
  have h15 := h14.append b15
  have b16 : CappedChainCertificate (5 / 854) (932 / 139315) (5035689209 / 1000000000000) Block16.cells :=
    ⟨Block16.fits, Block16.endpoint, Block16.upper⟩
  have h16 := h15.append b16
  have b17 : CappedChainCertificate (932 / 139315) (1 / 128) (6746939677 / 1000000000000) Block17.cells :=
    ⟨Block17.fits, Block17.endpoint, Block17.upper⟩
  have h17 := h16.append b17
  have b18 : CappedChainCertificate (1 / 128) (5 / 534) (9355266853 / 1000000000000) Block18.cells :=
    ⟨Block18.fits, Block18.endpoint, Block18.upper⟩
  have h18 := h17.append b18
  have b19 : CappedChainCertificate (5 / 534) (532 / 45475) (440169521 / 31250000000) Block19.cells :=
    ⟨Block19.fits, Block19.endpoint, Block19.upper⟩
  have h19 := h18.append b19
  have b20 : CappedChainCertificate (532 / 45475) (1 / 64) (1179767457 / 50000000000) Block20.cells :=
    ⟨Block20.fits, Block20.endpoint, Block20.upper⟩
  have h20 := h19.append b20
  have b21 : CappedChainCertificate (1 / 64) (5 / 214) (2917880567 / 62500000000) Block21.cells :=
    ⟨Block21.fits, Block21.endpoint, Block21.upper⟩
  have h21 := h20.append b21
  have b22 : CappedChainCertificate (5 / 214) (44 / 945) (7002005439 / 50000000000) Block22.cells :=
    ⟨Block22.fits, Block22.endpoint, Block22.upper⟩
  have h22 := h21.append b22
  have b23 : CappedChainCertificate (44 / 945) (9 / 20) (304899966729 / 125000000000) Block23.cells :=
    ⟨Block23.fits, Block23.endpoint, Block23.upper⟩
  have h23 := h22.append b23
  have hu : ((((((((((((((((((((((((254486947 / 500000000000) + (557876601 / 1000000000000)) + (153446181 / 250000000000)) + (334453589 / 500000000000)) + (29711949 / 40000000000)) + (829106009 / 1000000000000)) + (114756557 / 125000000000)) + (259405753 / 250000000000)) + (1181394001 / 1000000000000)) + (1337618529 / 1000000000000)) + (1550494737 / 1000000000000)) + (363468787 / 200000000000)) + (2127747961 / 1000000000000)) + (2564743329 / 1000000000000)) + (3149545437 / 1000000000000)) + (3899974557 / 1000000000000)) + (5035689209 / 1000000000000)) + (6746939677 / 1000000000000)) + (9355266853 / 1000000000000)) + (440169521 / 31250000000)) + (1179767457 / 50000000000)) + (2917880567 / 62500000000)) + (7002005439 / 50000000000)) + (304899966729 / 125000000000)) = areaUpper := by norm_num [areaUpper]
  rw [hu] at h23
  exact h23

theorem allCells_fits : cappedChainFits (1 / 512) allCells := allCells_certificate.1

theorem allCells_endpoint : cappedChainEnd (1 / 512) allCells = 9 / 20 :=
  allCells_certificate.2.1

theorem allCells_upper : cappedChainUpper allCells = areaUpper := allCells_certificate.2.2

theorem allCells_area_le : cappedChainArea allCells ≤ areaUpper := by
  rw [← allCells_upper]
  exact cappedChainArea_le_upper allCells_fits

theorem allCells_cover {β : ℝ} (hl : (1 / 512 : ℝ) < β) (hr : β ≤ 9 / 20) :
    ∃ x ∈ allCells, (x.1.lo : ℝ) < β ∧ β ≤ (x.1.hi : ℝ) := by
  apply cappedChain_cover allCells_fits (by norm_num at hl ⊢; exact hl)
  simpa only [allCells_endpoint, Rat.cast_div, Rat.cast_ofNat] using hr

theorem allCells_valid : ∀ x ∈ allCells, x.1.Valid := cappedChain_valid allCells_fits

theorem allCells_bounds {x : ArithmeticCell × ℚ} (hx : x ∈ allCells) :
    (1 / 512 : ℚ) ≤ x.1.lo ∧ x.1.hi ≤ 9 / 20 := by
  simpa only [allCells_endpoint] using cappedChain_mem_bounds allCells_fits hx

theorem allCells_primeMass_limit :
    Tendsto (fun N => finitePrimeMass (chainPrimePieces allCells) N / (N : ℝ) ^ 2)
      atTop (𝓝 (cappedChainArea allCells : ℝ)) := chainPrimeMass_limit allCells_fits

end Zeta5.Certificate.ExtendedArithmetic
