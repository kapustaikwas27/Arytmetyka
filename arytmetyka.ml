(******************************************)
(*           ZADANIE ARYTMETYKA           *)
(*        ROZWIAZANIE: MARCIN ZOLEK       *)
(*          RIWJU: ADAM GRELOCH          *)
(******************************************)

(*                  TYPY                  *)

type wartosc = {jeden: float; dwa: float; ile: int};; (* gdy ile = 1 typ wartosc reprezentuje przedzial [jeden; dwa], a gdy ile = 2 to [-nieskonczonosc; jeden] u [dwa; nieskonczonosc], natomiast ile >= 3 jest niepotrzebne *)
 
(*          PROCEDURY POMOCNICZE          *)

let dodaj a b = (* rozpisane przypadki dla dodawania dwoch przedzialow pojedynczych *)
    {jeden = a.jeden +. b.jeden; dwa = a.dwa +. b.dwa; ile = 1}
;;

let odejmij a b = (* rozpisane przypadki dla odejmowania dwoch przedzialow pojedynczych *)
    {jeden = a.jeden -. b.dwa; dwa = a.dwa -. b.jeden; ile = 1}
;;

let mnoz a b = (* rozpisane przypadki dla mnozenia dwoch przedzialow pojedynczych *)
    let gwiazdka x y = (* mnozenie dwoch liczb poszerzone o zasade 0 * (+/-)nieskonczonosc = 0 *)
        let typx = classify_float x in
        let typy = classify_float y in
    
        if (x = 0.0 || y = 0.0) && (typx = FP_infinite || typy = FP_infinite) then
            0.0
        else
            x *. y
    in

    if a.dwa <= 0.0 then
        if b.dwa <= 0.0 then
            {jeden = (gwiazdka a.dwa b.dwa); dwa = (gwiazdka a.jeden b.jeden); ile = 1}
        else if b.jeden < 0.0 && 0.0 < b.dwa then
            {jeden = (gwiazdka a.jeden b.dwa); dwa = (gwiazdka a.jeden b.jeden); ile = 1}
        else
            {jeden = (gwiazdka a.jeden b.dwa); dwa = (gwiazdka a.dwa b.jeden); ile = 1}
    else if a.jeden < 0.0 && 0.0 < a.dwa then
        if b.dwa <= 0.0 then
            {jeden = (gwiazdka a.dwa b.jeden); dwa = (gwiazdka a.jeden b.jeden); ile = 1}
        else if b.jeden < 0.0 && 0.0 < b.dwa then
            {jeden = min (gwiazdka a.jeden b.dwa) (gwiazdka a.dwa b.jeden); dwa = max (gwiazdka a.jeden b.jeden) (gwiazdka a.dwa b.dwa); ile = 1}
        else
            {jeden = (gwiazdka a.jeden b.dwa); dwa = (gwiazdka a.dwa b.dwa); ile = 1}
    else
        if b.dwa <= 0.0 then
            {jeden = (gwiazdka a.dwa b.jeden); dwa = (gwiazdka a.jeden b.dwa); ile = 1}
        else if b.jeden < 0.0 && 0.0 < b.dwa then
            {jeden = (gwiazdka a.dwa b.jeden); dwa = (gwiazdka a.dwa b.dwa); ile = 1}
        else
            {jeden = (gwiazdka a.jeden b.jeden); dwa = (gwiazdka a.dwa b.dwa); ile = 1}
;;

let dziel a b = (* rozpisane przypadki dla dzielenia dwoch przedzialow pojedynczych *)
    if b.jeden = 0.0 && b.dwa = 0.0 then
        {jeden = nan; dwa = nan; ile = 1}
    else if a.jeden = 0.0 && a.dwa = 0.0 then
        {jeden = 0.0; dwa = 0.0; ile = 1}
    else if b.jeden <= 0.0 && b.dwa >= 0.0 then
        if a.dwa <= 0.0 then
            if b.dwa = 0.0 then
                {jeden = a.dwa /. b.jeden; dwa = infinity; ile = 1}
            else if b.jeden < 0.0 && b.dwa > 0.0 then
                {jeden = a.dwa /. b.dwa; dwa = a.dwa /. b.jeden; ile = 2}
            else
                {jeden = neg_infinity; dwa = a.dwa /. b.dwa; ile = 1}
        else if a.jeden < 0.0 && a.dwa > 0.0 then
            {jeden = neg_infinity; dwa = infinity; ile = 1}
        else
            if b.dwa = 0.0 then
                {jeden = neg_infinity; dwa = a.jeden /. b.jeden; ile = 1}
            else if b.jeden < 0.0 && b.dwa > 0.0 then
                {jeden = a.jeden /. b.jeden; dwa = a.jeden /. b.dwa; ile = 2}
            else
                {jeden = a.jeden /. b.dwa; dwa = infinity; ile = 1}
    else
        if a.dwa <= 0.0 then
            if b.dwa < 0.0 then
                {jeden = a.dwa /. b.jeden; dwa = a.jeden /. b.dwa; ile = 1}
            else
                {jeden = a.jeden /. b.jeden; dwa = a.dwa /. b.dwa; ile = 1}
        else if a.jeden < 0.0 then
            if b.dwa < 0.0 then
                {jeden = a.dwa /. b.dwa; dwa = a.jeden /. b.dwa; ile = 1}
            else
                {jeden = a.jeden /. b.jeden; dwa = a.dwa /. b.jeden; ile = 1}
        else
            if b.dwa < 0.0 then
                {jeden = a.dwa /. b.dwa; dwa = a.jeden /. b.jeden; ile = 1}
            else
                {jeden = a.jeden /. b.dwa; dwa = a.dwa /. b.jeden; ile = 1}
;;

let zmiana a b operacja = (* oblicza wynikowy przedzial dla danej operacji i dwoch przedzialow (niekoniecznie pojedynczych) *)
    let wrzuc a lista = (* umieszcza przedzial na liscie, jesli przedzial jest dwuczesciowy to dzieli go na dwa *)
        if a.ile = 1 then
            a::lista
        else
            let b = {jeden = neg_infinity; dwa = a.jeden; ile = 1} in
            let c = {jeden = a.dwa; dwa = infinity; ile = 1} in
            
            c::b::lista
    in
    
    let rec sprawdz aktualna_lista oryginalna_lista = (* sprawdza czy przedzialy sa poprawne (ma znaczenie tylko dla przypadkow z nieskonczonymi przedzialami) *)
        match aktualna_lista with 
        | [] -> oryginalna_lista
        | glowa::ogon -> 
            if classify_float glowa.jeden = FP_nan || classify_float glowa.dwa = FP_nan || (glowa.jeden = neg_infinity && glowa.dwa = neg_infinity) || (glowa.jeden = infinity && glowa.dwa = infinity) then
                [{jeden = nan; dwa = nan; ile = 1}]
            else 
                sprawdz ogon oryginalna_lista
    in
 
    let rec oblicz lista_a lista_b cala_lista_b lista_c = (* oblicza sume kazdego przedzialu z lista_a z kazdym przedzialem z lista_b *)
        match (lista_a, lista_b) with 
        | ([], _) -> lista_c
        | (glowa_a::ogon_a, []) -> oblicz ogon_a cala_lista_b cala_lista_b lista_c
        | (glowa_a::ogon_a, glowa_b::ogon_b) -> 
            let przedzial = operacja glowa_a glowa_b in
            
            if classify_float przedzial.jeden = FP_nan || classify_float przedzial.dwa = FP_nan || classify_float glowa_a.jeden = FP_nan || classify_float glowa_a.dwa = FP_nan || classify_float glowa_b.jeden = FP_nan || classify_float glowa_b.dwa = FP_nan then
                [{jeden = nan; dwa = nan; ile = 1}]
            else
                oblicz lista_a ogon_b cala_lista_b ((wrzuc przedzial []) @ lista_c)
    in
    
    let porownaj a b = (* komparator do sortowania *)
        if a.jeden < b.jeden then
            -1
        else if a.jeden = b.jeden then
            0
        else
            1
    in
    
    let rec lacz lista1 poczatek koniec lista2 = (* laczenie przedzialow *)
        if lista1 = [] then
            {jeden = poczatek; dwa = koniec; ile = 1}::lista2
        else if (List.hd lista1).jeden >= poczatek && (List.hd lista1).jeden <= koniec then
                lacz (List.tl lista1) poczatek (max koniec (List.hd lista1).dwa) lista2
        else
            let ogon = List.tl lista1 in
            
            lacz ogon (List.hd lista1).jeden (List.hd lista1).dwa ({jeden = poczatek; dwa = koniec; ile = 1}::lista2)
    in
    
    (* glowny fragment sterujacy obliczaniem wyniku *)
    let lista_a = wrzuc a [] in 
    let lista_b = wrzuc b [] in 
    let lista_pom = oblicz lista_a lista_b lista_b [] in 
    let lista_c = sprawdz lista_pom lista_pom in 
    let glowa = List.hd lista_c in 
    
    if classify_float glowa.jeden = FP_nan || classify_float glowa.dwa = FP_nan || (glowa.jeden = neg_infinity && glowa.dwa = infinity) then (* przypadki szczegolne *)
        glowa
    else (* przypadki standardowe *)
        let posortowana_lista = List.sort porownaj lista_c in
        let zlaczona_lista = lacz posortowana_lista (List.hd posortowana_lista).jeden (List.hd posortowana_lista).dwa [] in
        
        if List.length zlaczona_lista = 1 then
            {jeden = (List.hd zlaczona_lista).jeden; dwa = (List.hd zlaczona_lista).dwa; ile = 1}
        else 
            {jeden = (List.hd (List.tl zlaczona_lista)).dwa; dwa = (List.hd zlaczona_lista).jeden; ile = 2}
;;

(*              KONSTUKTORY               *)         

let wartosc_dokladnosc x p =
    let przedzial1 = ((1.0 -. p /. 100.0) *. x) in
    let przedzial2 = ((1.0 +. p /. 100.0) *. x) in

    {jeden = min przedzial1 przedzial2; dwa = max przedzial1 przedzial2; ile = 1}
;;

let wartosc_od_do x y =
    {jeden = x; dwa = y; ile = 1}
;;

let wartosc_dokladna x =
    {jeden = x; dwa = x; ile = 1}
;;

(*                SELEKTORY               *)  

let in_wartosc a x =
    if a.ile = 1 then 
        if x >= a.jeden && x <= a.dwa then
            true
        else
            false
    else
        if x <= a.jeden || x >= a.dwa then
            true
        else
            false
;;

let min_wartosc a =
    let typ1 = classify_float a.jeden in
    
    if typ1 = FP_nan then
        nan
    else if a.ile = 2 || typ1 = FP_infinite then
        neg_infinity
    else 
        a.jeden
;;

let max_wartosc a =
    let typ2 = classify_float a.dwa in
    
    if typ2 = FP_nan then
        nan
    else if a.ile = 2 || typ2 = FP_infinite then
        infinity
    else 
        a.dwa
;;

let sr_wartosc a =
    let typ1 = classify_float a.jeden in
    let typ2 = classify_float a.dwa in
        
    if a.ile = 2 || typ1 = FP_nan || typ2 = FP_nan || (typ1 = FP_infinite && typ2 = FP_infinite) then
        nan
    else
        (a.jeden +. a.dwa) /. 2.0
;;

(*              MODYFIKATORY              *)    

let plus przedzial1 przedzial2 =
    zmiana przedzial1 przedzial2 dodaj
;;

let minus przedzial1 przedzial2 =
    zmiana przedzial1 przedzial2 odejmij
;;

let razy przedzial1 przedzial2 = 
    zmiana przedzial1 przedzial2 mnoz
;;

let podzielic przedzial1 przedzial2 =
    zmiana przedzial1 przedzial2 dziel
;;

(*                 KONIEC                 *)
