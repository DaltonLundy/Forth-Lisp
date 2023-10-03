( ----- lists and their words ----- )

: allocateNode ( addr )        2 cells allocate throw ;
: emptyNode ( addr )           allocateNode 0 over ! 0 over cell+ ! ;
: isEmpty  ( node -- bool )    dup @ 0= swap cell+ @ 0= and ;
: isNotEmpty  ( node -- bool ) dup @ 0<> swap cell+ @ 0<> or ;
: toNode ( addr -- node )      emptyNode 2dup ! nip ;
: stack ( list addr -- list )  toNode 2dup cell+ ! nip ;
: pop   ( list -- list addr )  dup @ swap  cell+ @ swap  ;
: nextNode ( list -- list )    dup isNotEmpty if cell+ @ endif ;
: lastNode ( list -- node )    dup isNotEmpty if begin dup cell+ @ isNotEmpty while nextNode repeat endif ;
: appendNode ( list addr -- list )   
                                    toNode over dup isNotEmpty if 
                                     lastNode nextNode over cell+ ! swap dup >r lastNode cell+ ! r>
                                    else
                                   ( emptylist newnode emptylist )
                                   over cell+ ! nip endif ;




( --- String parsing gen words --- )
: packString ( addr n -- addr )               2 cells allocate throw dup >r ! r> dup >r cell+ ! r> ;
: unPackString ( addr -- addr n )             dup cell+ @ swap @ ;
: nextChar  ( addr n -- addr' n' )            1- swap 1+ swap  ;
: currentChar  ( addr len -- addr len char )  over c@ ;
: isLParen     ( char -- bool )               40 = ;
: isRParen     ( char -- bool )               41 = ;
: isLower      ( char -- bool )               dup 123 <  swap 96 >  and ;
: isUpper      ( char -- bool )               dup 91  <  swap 64 >  and ;
: isAlpha      ( char -- bool )               dup isUpper swap isLower or ;
: isNum        ( char -- bool )               dup 58 < swap 47 > and ;
: isStrQuote   ( char -- bool )               34 = ;
: ischarQuote  ( char -- bool )               39 = ;
: isAtomic     ( char -- bool )               dup isAlpha swap isNum or ;
: isSemiColon  ( char -- bool )               59 = ;
: isSpace      ( char -- bool )               32 = ;
: isTic        ( char -- bool )               96 = ;
: getParen_cond ( addr len accum -- addr len accum bool )  rot dup c@ isRParen if 
                                                                     -rot dup 0<> 
                                                                    else
                                                                     -rot over 0 >
                                                                     endif
;
: getParen_    ( addr len accum -- addr len ) begin getParen_cond while 
                                              >r 
                                              over c@ isLParen if
                                                  r> 1+ >r
                                              endif
                                              over c@ isRParen if
                                                  r> 1- >r
                                              endif
                                              nextChar r> repeat
                                              drop 
                                              dup 0 < if 
                                                    s" getParen_ error " type cr .s cr abort
                                              endif
;

: getParen ( addr len -- addr len )           0 getParen_ ;
: skipSpace ( addr len -- addr len )          32 skip ;
: skipTab   ( addr len -- addr len )          9  skip ;
: skipSpaces ( addr len -- addr len )         skipTab skipSpace ;
: nextStrQuote ( addr len -- addr len )       begin 
                                              dup -1 > if over c@ isStrQuote 0= else 0 endif while 
                                              nextChar repeat ;

( --- Atoms --- )
1 Constant AtomFlag
: allocateAtom ( atom )          cell 1+ allocate throw ;
: mkAtom  ( addr len -- addr ) packString allocateAtom AtomFlag over c! 2dup 1+ ! nip  ;
: parseAtom ( addr len -- addr len atom ) 2dup 
                                          begin over c@ isAtomic while nextChar repeat 
                                          ( OGList OGLen newList newLen )
                                           swap ( OGList OGLen newLen newList )
                                           >r   ( OGList OGLen newLen )
                                           dup >r ( OGList OGLen newLen )
                                           -     ( OGList difflen ) 
                                           mkAtom ( atom )
                                           r> r>    ( Atom newLen newList )
                                           swap     ( Atom newList newLen )
                                           rot      ( newList newLen Atom )
;

: unPackAtom ( addr -- addr len )  1+ @ dup cell+ @ swap @ ;
: copyAtom ( addr1 -- addr2 )  unpackAtom  save-mem  mkAtom ;

( --- lisp lists --- )
2 Constant ListFlag 
: allocateLispList ( addr ) cell 1+ allocate throw ;
: mkLispList ( list -- lisplist ) allocatelispList dup ListFlag swap c! 2dup 1+ ! nip ;
: unpackLispList ( lispLIst -- list ) @ 1+ @ ;

( --- Strings --- )
3 Constant StrFlag
: allocateString ( addr ) cell 1+ allocate throw ;
: MkString ( addr len -- addr ) mkAtom strFlag over c! ;
: unPackString_ ( addr -- addr len ) unPackAtom ;
: parseString  ( addr len -- addr len str ) 2dup nextStrQuote ( addr len newaddr newlen )
                                            swap >r           ( addr len newlen )
                                            2dup -            ( addr len newlen diff )
                                            3 roll swap       ( len newlen addr diff )
                                            mkString          ( len newlwn str )
                                            rot               ( newlen str len )
                                            drop              ( newlen str ) 
                                            r>                ( newlen str newaddr )
                                            rot               ( str newaddr newlen )
                                            rot               ( newlen newaddr str )
;

: copyStr unPackString_ save-mem MkString ;

( ----- Thunks ----- )
4 Constant ThunkFlag
: allocateThunk allocateLispList ;
: mkThunk  mkLispList ThunkFlag over c! ;
: unpackthunk unpackLispList ;

Defer copyLispList 

: copyLispList_ ( newlist oldlist -- newlist ) 
  begin
	  dup isEmpty 0= while
	  dup >r
	  @ 
	  dup c@ AtomFlag = if
	    copyAtom AppendNode
	  else
	  dup c@ ListFlag = if
            1+ @ copyLispList mkLispList AppendNode
          else 
            abort
	  endif endif
	  r>
          nextnode 
  repeat 
  drop
;

:noname emptyNode swap copyLispList_ ; is copyLispList

( --- Globals --- )
Variable return_stack
emptyNode return_stack !
: toReturnStack ( addr len -- )  packString return_stack @ swap stack return_stack ! ;
: popReturnStack ( -- addr len ) return_stack @ pop swap  >r unPackString r> return_stack ! ;

( --- Main Parsing --- )
Defer parseList_ ( list addr len -- list )

: parseAtomsInList ( list addr len -- list )
	begin 

          over c@ isRParen 0=  while

                  over c@ isLParen if
		    nextchar 2dup getParen toReturnStack ( List addr len )
		     emptyNode       ( list addr len emptylist )
		     -rot            ( list emptylist addr len )
		     parseList_ mkLispList     ( list newlist ) 
		     appendNode          ( list )
		     popReturnStack  ( list addr len )
                     nextchar
                 else
  
                 over c@ isAtomic if
			 parseAtom ( list addr len atom )
			 3 roll    ( addr len atom list )
			 swap      ( addr len list atom )
			 appendNode    ( addr len list )
			 -rot      ( list addr len )
                 else
                 
                 over c@ isStrQuote if
                         nextchar
                         parseString
			 3 roll    ( addr len atom list )
			 swap      ( addr len list atom )
			 appendNode    ( addr len list )
			 -rot      ( list addr len )
                         nextchar
                 else
                 
                 over c@ isTic if
		    nextchar 
                     skipspaces
                     over c@ isLParen if nextchar endif
                     2dup
                     getParen toReturnStack ( List addr len )
		     emptyNode       ( list addr len emptylist )
		     -rot            ( list emptylist addr len )
		     parseList_ mkThunk     ( list newlist ) 
		     appendNode          ( list )
		     popReturnStack  ( list addr len )
                     nextchar
                 else
                 nextchar endif endif endif endif
	repeat
        drop drop
;

:noname skipSpaces parseAtomsInList ; is ParseList_

: parseList ( addr len -- list ) emptyNode -rot 40 scan nextchar parseList_ ;

( --- Serialization --- )

Variable indent
0 indent !

4 constant margins 

: increaseIndent indent @ margins + indent ! ;
: decreaseIndent indent @ margins - indent ! ;

: emitMargin indent @ 0 ?do 32 emit loop ;


: showAtom unpackAtom type ;
: showString 34 emit showAtom 34 emit ;

Defer serialize ( lisplist -- )

: serialHelper ( lisplist -- )
  begin
  dup if dup IsEmpty 0= else 0 endif while
	   dup @
	     dup c@ AtomFlag = if 
                32 emit
		showAtom
		32 emit
	     else
	     dup c@ StrFlag = if 
                32 emit
		showString
		32 emit
             else
	       dup c@ ListFlag = if
                increaseIndent
                1+ @  serialize
                decreaseIndent
		32 emit
                drop
             else
	       dup c@ ThunkFlag = if
                96 emit
                32 emit
                increaseIndent
                1+ @  serialize
                decreaseIndent
		32 emit
                drop
	   endif endif endif endif
  nextNode
  repeat
  41 emit
;

:noname ( lisplist -- )
  cr
  emitMargin 
  40 emit 
  dup
  dup isEmpty if 41 emit else 
  serialHelper endif
  drop 
; is serialize


( --- Dictionaries and their words --- )

 : addEntry ( Dict lispList addr len )  ;
( ----- Semantics ----- ) 

  ( -- keyword -- )
: lambda_KW s" lambda" ;
: defun_KW  s" defun"  ;
: eval_KW   s" eval"   ;


s" ( Lambda x ( x y ) ) " parseList copylispList serialize cr
