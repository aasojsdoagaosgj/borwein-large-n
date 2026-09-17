import Borwein.RoundedWeightChunk00
import Borwein.RoundedWeightChunk01
import Borwein.RoundedWeightChunk02
import Borwein.RoundedWeightChunk03
import Borwein.RoundedWeightChunk04
import Borwein.RoundedWeightChunk05
import Borwein.RoundedWeightChunk06
import Borwein.RoundedWeightChunk07
import Borwein.RoundedWeightChunk08
import Borwein.RoundedWeightChunk09
import Borwein.RoundedWeightChunk10
import Borwein.RoundedWeightChunk11
import Borwein.RoundedWeightChunk12
import Borwein.RoundedWeightChunk13
import Borwein.RoundedWeightChunk14
import Borwein.RoundedWeightChunk15

namespace Borwein.RoundedWeightChecks

theorem all_checks (d : Fin 4) (i : ℕ) (hi : i < 400) : Borwein.RoundedWeightData.Checks d i := by
  by_cases h0 : i < 25
  · have hj : i-0 < 25 := by omega
    have h := Borwein.RoundedWeightChunk00.checked d ⟨i-0,hj⟩
    have he : 0+(i-0) = i := by omega
    simpa only [he] using h
  by_cases h1 : i < 50
  · have hj : i-25 < 25 := by omega
    have h := Borwein.RoundedWeightChunk01.checked d ⟨i-25,hj⟩
    have he : 25+(i-25) = i := by omega
    simpa only [he] using h
  by_cases h2 : i < 75
  · have hj : i-50 < 25 := by omega
    have h := Borwein.RoundedWeightChunk02.checked d ⟨i-50,hj⟩
    have he : 50+(i-50) = i := by omega
    simpa only [he] using h
  by_cases h3 : i < 100
  · have hj : i-75 < 25 := by omega
    have h := Borwein.RoundedWeightChunk03.checked d ⟨i-75,hj⟩
    have he : 75+(i-75) = i := by omega
    simpa only [he] using h
  by_cases h4 : i < 125
  · have hj : i-100 < 25 := by omega
    have h := Borwein.RoundedWeightChunk04.checked d ⟨i-100,hj⟩
    have he : 100+(i-100) = i := by omega
    simpa only [he] using h
  by_cases h5 : i < 150
  · have hj : i-125 < 25 := by omega
    have h := Borwein.RoundedWeightChunk05.checked d ⟨i-125,hj⟩
    have he : 125+(i-125) = i := by omega
    simpa only [he] using h
  by_cases h6 : i < 175
  · have hj : i-150 < 25 := by omega
    have h := Borwein.RoundedWeightChunk06.checked d ⟨i-150,hj⟩
    have he : 150+(i-150) = i := by omega
    simpa only [he] using h
  by_cases h7 : i < 200
  · have hj : i-175 < 25 := by omega
    have h := Borwein.RoundedWeightChunk07.checked d ⟨i-175,hj⟩
    have he : 175+(i-175) = i := by omega
    simpa only [he] using h
  by_cases h8 : i < 225
  · have hj : i-200 < 25 := by omega
    have h := Borwein.RoundedWeightChunk08.checked d ⟨i-200,hj⟩
    have he : 200+(i-200) = i := by omega
    simpa only [he] using h
  by_cases h9 : i < 250
  · have hj : i-225 < 25 := by omega
    have h := Borwein.RoundedWeightChunk09.checked d ⟨i-225,hj⟩
    have he : 225+(i-225) = i := by omega
    simpa only [he] using h
  by_cases h10 : i < 275
  · have hj : i-250 < 25 := by omega
    have h := Borwein.RoundedWeightChunk10.checked d ⟨i-250,hj⟩
    have he : 250+(i-250) = i := by omega
    simpa only [he] using h
  by_cases h11 : i < 300
  · have hj : i-275 < 25 := by omega
    have h := Borwein.RoundedWeightChunk11.checked d ⟨i-275,hj⟩
    have he : 275+(i-275) = i := by omega
    simpa only [he] using h
  by_cases h12 : i < 325
  · have hj : i-300 < 25 := by omega
    have h := Borwein.RoundedWeightChunk12.checked d ⟨i-300,hj⟩
    have he : 300+(i-300) = i := by omega
    simpa only [he] using h
  by_cases h13 : i < 350
  · have hj : i-325 < 25 := by omega
    have h := Borwein.RoundedWeightChunk13.checked d ⟨i-325,hj⟩
    have he : 325+(i-325) = i := by omega
    simpa only [he] using h
  by_cases h14 : i < 375
  · have hj : i-350 < 25 := by omega
    have h := Borwein.RoundedWeightChunk14.checked d ⟨i-350,hj⟩
    have he : 350+(i-350) = i := by omega
    simpa only [he] using h
  have hj : i-375 < 25 := by omega
  have h := Borwein.RoundedWeightChunk15.checked d ⟨i-375,hj⟩
  have he : 375+(i-375) = i := by omega
  simpa only [he] using h

end Borwein.RoundedWeightChecks


