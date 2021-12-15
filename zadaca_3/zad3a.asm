//R0 baza 
//R1 eksponent
//spremi u R2 

@R0
D = M
@baza
M = D

@R1
D=M 
@eksponent
M=D

@j
M = 1   // j postavi na jedan 
(PotenciranjeS)
    @R1
    D = M

    @j
    D = M - D    // od eksponenta oduzimaj j 

    @PotenciranjeE
    D; JGE   // ako je D>=0 skoci

    @LoopS
    0; JMP   // bezuvjetno skoci na kraj 


(LoopS)
@i
M = 0
    (LoopStart)
        @R0
        D = M

        @i
        D = M - D  // od baze oduzimaj i 

        @LoopE
        D; JGE   // ako je  D>= 0 


        @baza 
        D = M

        @k
        M = M + D   

        @i
        M = M + 1

        @LoopStart
        0; JMP

    (LoopE)

    @k
    D = M

    @baza
    M = D

    @k
    M = 0

    @j
    M = M + 1

    @PotenciranjeS
    0; JMP

(PotenciranjeE)
@baza
D = M
@R2
M = D

(END)
@END
0; JMP



