/* GestServ
 * Author: 
 * Creation date: 04/12/13
 */
MACHINE
    GestServ
    
    SETS
	    SERVICES
	    ; PROCESSUS
	    ; PROFILS
	    ; TYPE_ACCES = {CONTRAINT,NON_CONTRAINT}
	    ; ETAT = {ACTIF,ETEINT}
	    ; TYPE_EXCLUSIF = {EXCLUSIF, NON_EXCLUSIF}
	    ; NOMS
    
	VARIABLES
    	lesServices
	    , lesProfils
	    , lesProcessus
	    , lesNoms
	    , nomService
	    , estDansEtat
	    , profilAssocie
	    , donneAcces
	    , aSouscrit
	    , utilise
	    , estDeType
	    , typeAcces	    
    
	INVARIANT
    	lesServices <: SERVICES
		& lesProfils <: PROFILS
		& lesProcessus <: PROCESSUS
		& lesNoms <: NOMS
		& nomService : lesServices >-> lesNoms
		& estDansEtat : lesServices --> ETAT
		& profilAssocie : lesProcessus --> lesProfils
		& donneAcces : lesProfils <-> lesServices
		& aSouscrit : lesProcessus <-> lesServices
		& utilise : lesProcessus +-> lesServices
		& estDeType : lesServices --> TYPE_ACCES
		& typeAcces : lesServices --> TYPE_EXCLUSIF
    	
    
	INITIALISATION
	    lesServices := {}
	    || lesProfils := {}
	    || lesProcessus := {}
	    || lesNoms := {}
	    || nomService := {}
	    || estDansEtat := {}
	    || profilAssocie := {}
	    || donneAcces := {}
		|| aSouscrit := {}
	    || utilise := {}
	    || estDeType := {}
	    || typeAcces := {}
	    
    	
 	OPERATIONS
 	    ajouterService(ss,name) = 
 	    PRE
 	        ss : SERVICES
 	        & ss /: lesServices
 	        & name : NOMS
 	        & name /: lesNoms
 	    THEN
 	        lesServices := lesServices \/ {ss}
 	        || lesNoms := lesNoms \/ {name}
 	        || nomService := nomService \/ {(ss |-> name)}
 	        || estDansEtat := estDansEtat \/ {(ss |-> ETEINT)}
 	        || estDeType := estDeType \/ {(ss |-> NON_CONTRAINT)}
 	        || typeAcces := typeAcces \/ {(ss |-> NON_EXCLUSIF)}
 	    END;
 	    
 	    supprimerService(ss) = 
 	    PRE
 	        ss : SERVICES
 	        & ss : lesServices
 	        & estDansEtat(ss) = ETEINT
 	        & ss : dom(estDansEtat)
 	        & ss : dom(nomService)
		THEN
    		ANY name WHERE name : NOMS & name = nomService(ss) THEN
		    	 donneAcces := donneAcces |>> {ss}
		    	|| aSouscrit := aSouscrit |>> {ss}
		    	|| utilise :=  utilise |>> {ss}
		    	|| estDansEtat := {ss} <<| estDansEtat
		    	|| estDeType := {ss} <<| estDeType
		    	|| typeAcces := {ss} <<| typeAcces
		    	|| nomService := {ss} <<| nomService
		    	|| lesNoms := lesNoms - {name}
		   	 	|| lesServices := lesServices - {ss}
		    END
		END;
		
		contraindreService(ss,prof) = 
		PRE
		    ss : SERVICES
		    & ss : lesServices
		    & prof : PROFILS
		    & prof : lesProfils
		    & (prof,ss) /: donneAcces
		THEN
		    estDeType(ss) := CONTRAINT
		    || donneAcces := donneAcces \/ {(prof |-> ss)}
		END;
		
		supprimerRestriction(ss,prof) =
		PRE
		    ss : SERVICES
		    & ss : lesServices
		    & prof : PROFILS
		    & prof : lesProfils
		    & (prof,ss) : donneAcces
		THEN
		    donneAcces := donneAcces - {(prof |-> ss)}
		    || 	IF (donneAcces |> {ss} = {})
		    	THEN estDeType(ss) := NON_CONTRAINT
		        END
		END;
 	    
 	    interrompreService(ss) =
 	    PRE
 	        ss : SERVICES
 	        & ss : lesServices
 	        & estDansEtat(ss) = ACTIF
 	    THEN
 	        estDansEtat(ss) := ETEINT
        END;
        
        activerService(ss) = 
        PRE
            ss : SERVICES
            & ss : lesServices
			& estDansEtat(ss) = ETEINT
		THEN
    		estDansEtat(ss) := ACTIF
        END;
        
        ajouterProfil(prof) = 
        PRE
            prof : PROFILS
            & prof /: lesProfils
        THEN
            lesProfils := lesProfils \/ {prof}
        END;
        
        ajouterProcessus(proc,prof) = 
        PRE
            proc : PROCESSUS
            & prof : PROFILS
            & proc /: dom(profilAssocie)
            & proc /: lesProcessus
            & prof : lesProfils
        THEN
            lesProcessus := lesProcessus \/ {proc}
            || profilAssocie := profilAssocie \/ {(proc |-> prof)}
        END;
        
        supprimerProcessus(proc) = 
        PRE
            proc : PROCESSUS
            & proc : lesProcessus
        THEN
            lesProcessus := lesProcessus - {proc}
            || profilAssocie := {proc} <<| profilAssocie
            || aSouscrit := {proc} <<| aSouscrit
            || utilise := {proc} <<| utilise
        END;
        
        modifierProfilProcessus(proc,prof) = 
        PRE
            proc : PROCESSUS
            & proc : lesProcessus
            & prof : PROFILS
            & prof : lesProfils
        THEN
            profilAssocie(proc) := prof
        END;
        
        souscrireService(proc,ss) = 
        PRE
            proc : PROCESSUS
            & proc : lesProcessus
            & ss : SERVICES
            & ss : lesServices
            & (proc,ss) /: aSouscrit
        THEN
            aSouscrit := aSouscrit \/ {(proc |-> ss)}
        END;
        
        suspendreSouscription(proc,ss) = 
        PRE
            proc : PROCESSUS
            & proc : lesProcessus
            & ss : SERVICES
            & ss : lesServices
            & (proc,ss) : aSouscrit
        THEN
            aSouscrit := aSouscrit - {(proc |-> ss)}
        END;
        
        res <-- verificationAccesService(ss) =
        PRE
            ss : SERVICES
            & ss : lesServices
        THEN
            IF(typeAcces(ss) = EXCLUSIF) THEN
                IF(utilise |>> {ss} = {}) THEN
                    res := TRUE
                ELSE
                    res := FALSE
                END
            ELSE
                res := TRUE
            END
        END;
        
        res <-- demanderService(proc,ss) = 
        PRE
            proc : PROCESSUS
            & proc : lesProcessus
            & ss : SERVICES
            & ss : lesServices
            & estDansEtat(ss) = ACTIF
            & (profilAssocie(proc),ss) : donneAcces
            & (proc,ss) /: utilise
            & ((typeAcces(ss) = NON_EXCLUSIF) or (typeAcces(ss) = EXCLUSIF & utilise |>> {ss} = {}))
        THEN
           	utilise(proc) := ss
            || res := ss
        END;

        libererService(proc,ss) = 
        PRE
            proc : PROCESSUS
            & proc : lesProcessus
            & ss : SERVICES
            & ss : lesServices
            & (proc,ss) : utilise
        THEN
            utilise := utilise - {(proc |-> ss)}
        END

END
