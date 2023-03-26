; This works only on Wio Lite RISC V
; https://wiki.seeedstudio.com/Wio_Lite_RISC_V_GD32VF103_with_ESP8266/

(io-write 
        (+ 0x40021000 0x18) 
        (<< 0b0001 2)) 

; GPIO A 
(define base 0x40010800)

; Configure output mode
(io-write 
        (+ base 0x04) 
        ; Push-pull output, output mode (50MHz)
        0x3)

; Clear bit
(io-write 
        (+ base 0x18) 
        (<< 0b0001 8))

; Set bit (lighting)
(io-write 
        (+ 0x40010800 0x10) 
        (<< 0b0001 8))
