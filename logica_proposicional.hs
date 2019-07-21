--David Savary Martinez

type Var = String -- nombres de variables
data FProp = V Var | No FProp | Y FProp FProp | O FProp FProp | Si FProp FProp | Sii FProp FProp deriving Read

f1 = Si (No (V "p")) (Si (V "p") (Y (V "q") (No (V "q"))))
f2 = Y (V "p") (Si (No (V "q")) (No (V "p")))
f3 = Y (V "p") (Y (V "q") (O (No (V "q")) (V "r")))
f4 = Si (No (V "p")) (V "q")
f5 = O (No (V "p")) (V "p")
f6 = Y (No (V "q")) (V "p")
f7 = O (O (No (V "q")) (V "q")) (O (No (V "p")) (V "p"))
f8 = O (V "p") (No (V("p")))

-------- Instancias Parte Basica ----------

instance Eq FProp where
 form1 == form2 = compIguales form1 form2

instance Ord FProp where
 form1 <= form2 = consecuencia form1 form2

instance Show FProp where
 show form = mostrar form

-------- Funciones Parte Basica -----------

vars :: FProp -> [Var] --Calcula una lista con las variables de la expresion x sin repeticiones.
--Si la expresion tiene dos partes, concatena sin repeticiones las variables de ambas partes.
vars (V x) = [x] --Si la expresion es una variable, se devuelve la única variable que contiene
vars (No x) = vars x --Si la expresion es una negacion, se ignora la negacion y se buscan las variables del resto de la expresión
vars (Y x1 x2) = sinDupl ((vars x1)++(vars x2))
vars (O x1 x2) = sinDupl ((vars x1)++(vars x2))
vars (Si x1 x2) = sinDupl ((vars x1)++(vars x2))
vars (Sii x1 x2) = sinDupl ((vars x1)++(vars x2))

tautologia :: FProp -> Bool -- Calcula si una expresion es una tautologia comprobando si devuelve true a cada posible combinacion de valores de sus variables
tautologia expr = foldl' (&&) (resultados expr (listaVarVal expr))

satisfactible :: FProp -> Bool -- Calcula si existe una combinacion de valores que hagan cierta una expresión, probando todas las posibles combinaciones.
satisfactible expr = foldl' (||) (resultados expr (listaVarVal expr))

consecuencia :: FProp -> FProp -> Bool -- Comprueba si una expresion es consecuencia logica de otra. Comprueba que ambas expresiones tienen las mismas variables.
-- Luego comprueba que para todas las entradas de expr1, expr2 sea consecuencia de expr1. True si expr2 es consecuencia de expr1
consecuencia expr1 expr2 = (mismasVariables expr1 expr2) && (foldl' (&&) (map (consecuenciaOk) (zip (resultados expr1 lstVal) (resultados expr2 lstVal))))
 where lstVal = listaVarVal expr1

equivalente :: FProp -> FProp -> Bool-- Comprueba si una expresion es equivalente logica de otra. Comprueba que ambas expresiones tienen las mismas variables.
-- Luego comprueba que para todas las entradas de expr1, expr2 sea equivalente a expr1. True si expr2 es equivalente a expr1
equivalente expr1 expr2 = (mismasVariables expr1 expr2) && (foldl' (&&) (map (equivalenteOk) (zip (resultados expr1 lstVal) (resultados expr2 lstVal))))
 where lstVal = listaVarVal expr1

consecuencias :: [FProp] -> [(FProp,[FProp])] --Dada una lista de expresiones devuelve una lista de cada formula emparejada con las formulas que son consecuencia de ella
consecuencias lst = [(x,(todCons x lst)) | x <- lst]

equivalentes :: [FProp] -> [[FProp]] --Dada una lista de expresiones devuelve una lista de cada formula emparejada con las formulas que son equivalentes ella
equivalentes lst = sinDuplLst [todEquiv x lst | x <- lst]



-------- Parte Opcional --------------------------
main :: IO () -- Ejecuta el menú de I/O
main = do
 putStrLn "1- Comprobar si una formula es satisfactible"
 putStrLn "2- Comprobar si una formula es una tautologia"
 putStrLn "3- Comprobar si una formula es consecuencia de otra"
 putStrLn "4- Comprobar si una formula es equivalente a otra"
 putStrLn "5- Comprobar consecuencias en una lista de formulas"
 putStrLn "6- comprobar equivalencias en una lista de formulas"
 putStrLn "Elige una opción:"
 line <- getLine
 case line of
       "1" -> opcSatisfactible
       "2" -> opcTautologia
       "3" -> opcConsec
       "4" -> opcEquiv
       "5" -> opcConsecLst
       "6" -> opcEquivLst



-------- Funciones auxiliares Parte Basica --------

sinDupl :: (Eq a) => [a] -> [a] --Elimina los duplicados de una lista
sinDupl [x] = [x] --Si la lista contiene solo un elemento se devuelve ese elemento
sinDupl (x:xs) = x : [k | k <- sinDupl(xs), k /= x] --Si la lista tiene mas de un elemento, se quitan las repeticiones de la lista
-- sin la cabeza y luego se eliminan los elementos que sean igual a la cabeza.


calcula ::  FProp -> [(Var, Bool)] -> Bool -- Dada una expresion y una lista de tuplas que dan valores a las variables, calcula el valor de la expresión
calcula (V val) lst = busca lst val
calcula (No val) lst = not (calcula val lst)
calcula (Y val1 val2) lst = (calcula val1 lst) && (calcula val2 lst)
calcula (O val1 val2) lst = (calcula val1 lst) || (calcula val2 lst)
calcula (Si val1 val2) lst
 | (calcula val1 lst) && (not (calcula val2 lst)) = False
 | otherwise = True
calcula (Sii val1 val2) lst
 | (calcula val1 lst) == (calcula val2 lst) = True
 | otherwise = False


busca :: [(Var, Bool)] -> Var -> Bool -- Dada una var y una lista de tuplas de variables con un valor, devuelve el valor de var
busca [(y, yv)] _ = yv
busca ((y, yv):lst) val
 | y == val = yv
 | otherwise = busca lst val

listaVarVal :: FProp -> [[(Var, Bool)]] -- Lista emparejada de variables con booleanos, de forma que se cubran todas las combinaciones de valores posibles
listaVarVal expr = map (zip (vars expr)) (comb (length (vars expr)))

comb :: Int -> [[Bool]] -- Devuelve una lista de listas de longitud n contodas las posibles combinaciones de true y false
comb 0 = [[]]
comb n = map (True:) (comb (n - 1)) ++ map (False:) (comb (n-1))

resultados :: FProp -> [[(Var, Bool)]] -> [Bool] -- Dada una expresion y una lista de entradas devuelve una lista con los valores de cada una de las entradas
resultados expr lst = map (calcula expr) lst

foldl' :: (a -> a -> a) -> [a] -> a -- Aplica lafuncion foldl a una lista de valores utilizando el primero como elemento auxiliar
foldl' f (x:xs) = foldl f x xs

agrupaValores :: FProp -> FProp -> [(Bool, Bool)] --Dadas dos expresiones con las mismas variables devuelve tuplas con los resultados de ambas para la misma entrada
agrupaValores expr1 expr2 = zip (map (calcula expr1) vars) (map (calcula expr2) vars)
 where
 vars = listaVarVal expr1

consecuenciaOk :: (Bool, Bool) -> Bool -- Hace la operacion de consecuencia con los valores de la tupla. True si y es consecuencia de x
consecuenciaOk (x,y) = (x && y) || not(x)

equivalenteOk :: (Bool, Bool) -> Bool -- Hace la operacion de equivalente con los valores de la tupla
equivalenteOk (x,y) = x == y

mismasVariables :: FProp -> FProp -> Bool -- Compreba que las dos expresiones tienen las mismas variables
mismasVariables expr1 expr2 = 
 (length(vs1)==length(vs2)) &&
 [ x | x <- vs1, not (elem x vs2)] == [] &&
 [ y | y <- vs2, not (elem y vs1)] == []
 where vs1 = vars expr1
       vs2 = vars expr2

todCons :: FProp -> [FProp] -> [FProp] -- Dada una formula y una lista de formulas devuelve otra lista con las formulas que sean consecuencia de la primera.
todCons x [] = [] --Si ya no quedan formulas en la lista se devuelve una lista vacia.
todCons x (l:ls) --Si quedan formulas en la lista
 | (consecuencia x l) == True = l:(todCons x ls) --Si la primera formula de la lista es consecuencia de x, se llama a esta funcion con el resto de la lista y se añade la cabecera
 | otherwise = (todCons x ls) -- Si la prmera formula no es consecuencia de x, se decarta esta primera formula.

todEquiv :: FProp -> [FProp] -> [FProp] -- Dada una formula y una lista de formulas devuelve otra lista con las formulas que sean equivalentes a la primera.
todEquiv x [] = []
todEquiv x (l:ls) --Si quedan formulas en la lista
 | (equivalente x l) == True = l:(todEquiv x ls) --Si la primera formula de la lista es equivalente a x, se llama a esta funcion con el resto de la lista y se añade la cabecera
 | otherwise = (todEquiv x ls) -- Si la prmera formula no es equivalente a x, se decarta esta primera formula.

contenida :: (Foldable t, Eq a) => [a] -> t a -> Bool -- Devuelve si la segunda lista contiene todos los elementos de la primera
contenida [] lst2 = True
contenida (x:xs) lst2 = elem x lst2 && contenida xs lst2

listIguales :: Eq a => [a] -> [a] -> Bool --Devuelve true si dos listas contienen los mismos elementos
listIguales lst1 lst2 = contenida lst1 lst2 && contenida lst2 lst1

sinDuplLst :: Eq a => [[a]] -> [[a]] -- Devuelve una lista de listas eliminando listas que contengan los mismos elementos que otra
sinDuplLst [x] = [x]
sinDuplLst (x:xs) = x : [k | k <- sinDuplLst(xs), not(listIguales k x)]

compIguales :: FProp -> FProp -> Bool -- Dadas 2 expresiones devuelve si son iguales estructuralmente
compIguales (V form1) (V form2) = form1 == form2
compIguales (No form1) (No form2) = form1 == form2
compIguales (O form11 form12) (O form21 form22) = ((form11==form21) && (form12==form22)) || ((form11==form22) && (form12==form21))
compIguales (Y form11 form12) (Y form21 form22) = ((form11==form21) && (form12==form22)) || ((form11==form22) && (form12==form21))
compIguales (Si form11 form12) (Si form21 form22) = ((form11==form21) && (form12==form22))
compIguales (Sii form11 form12) (Sii form21 form22) = ((form11==form21) && (form12==form22)) || ((form11==form22) && (form12==form21))
compIguales _ _ = False

mostrar :: FProp -> [Char] --Muestra laformula deforma amigable
mostrar (V val) = val
mostrar (No form) = "~(" ++ mostrar form ++ ")"
mostrar (O form1 form2) = "("++ mostrar form1 ++ ") V (" ++ mostrar form2 ++ ")"
mostrar (Y form1 form2) = "("++ mostrar form1 ++ ") ^ (" ++ mostrar form2 ++ ")"
mostrar (Si form1 form2) = "("++ mostrar form1 ++ ") -> (" ++ mostrar form2 ++ ")"
mostrar (Sii form1 form2) = "("++ mostrar form1 ++ ") <-> (" ++ mostrar form2 ++ ")"




-------- Funciones auxiliares parte opcional ----------
getForm :: IO FProp -- Devuelve una formula introducida por consola
getForm = do line <- getLine
             return (read line::FProp)

getInt :: IO Int -- Devuelve un int introducido por consola
getInt = do line <- getLine
            return (read line::Int)

opcSatisfactible :: IO () -- Pide una formula por consola y escribe si es satisfactible o no
opcSatisfactible = do
 putStrLn "Escribe la formula:"
 form1 <- getForm
 if (satisfactible form1) == True then putStrLn "La formula es satisfactible" else putStrLn "La formulano es satisfactible"

opcTautologia :: IO () -- Pide una formula por consola y escribe si es una tautologia o no
opcTautologia = do
 putStrLn "Escribe la formula:"
 form1 <- getForm
 if (tautologia form1) == True then putStrLn "La formula es una tautologia" else putStrLn "La formulano es una tautologia"

opcConsec :: IO () -- Pide dos formulas por consola y escribe si la segunda es consecuencia de la primera
opcConsec = do
 putStrLn "Escribe la consecuencia:"
 form1 <- getForm
 putStrLn "Escribe la formula de la que es (o no) consecuencia:"
 form2 <- getForm
 if (consecuencia form1 form2) == True then putStrLn "La segunda formula es una consecuencia de la primera" else putStrLn "La segunda formula no es una consecuencia de la primera"

opcEquiv :: IO () -- Pide dos formulas por consola y escribe si son equivalenets
opcEquiv = do
 putStrLn "Escribe la primera formula:"
 form1 <- getForm
 putStrLn "Escribe la segunda formula:"
 form2 <- getForm
 if (equivalente form1 form2) == True then putStrLn "Las formulas son equivalentes" else putStrLn "Las formulas no so equivalentes"

opcConsecLst :: IO() -- Pide un numero y a continuacion pide ese numero de formulas.
--A contibuacion escribe cada formula agrupada con las formulas que sean consecuancias suyas
opcConsecLst = do
 putStrLn "Escribe el tamaño de la lista de formulas:"
 num <- getInt
 lst <- getLst num
 print (consecuencias lst)

opcEquivLst :: IO() -- Pide un numero y a continuacion pide ese numero de formulas.
--A contibuacion escribe cada formula agrupada con las formulas que sean equivalentes
opcEquivLst = do
 putStrLn "Escribe el tamaño de la lista de formulas:"
 num <- getInt
 lst <- getLst num
 print (equivalentes lst)

getLst :: (Eq t, Num t) => t -> IO [FProp] -- Devuelve una lista con n formulas logicas escritas en consola
getLst 1 = do
  putStrLn "Escribe una formula:"
  form <- getForm
  return (form:[])
getLst num = do
 putStrLn "Escribe una formula:"
 form <- getForm
 forms <- getLst (num - 1)
 return (form:forms)