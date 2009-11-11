-- Normal Forms in Lua
-- Adolfo Neto (DAINF-UTFPR) http://www.dainf.ct.utfpr.edu.br/~adolfo
-- October 2009

-- Utilitary functions

IMP="->"
AND="^"
OR="v"
NOT="!"

A="A"
B="B"
C="C"

function tabToString(table) 
  result="{"
  for i, value in ipairs (table) do
    if type(value) == "table" then
        result = result .. tabToString(value)
      else
        result = result .. value
    end
    if not (i == #table) then
       result = result .. ","
    end   
  end
  result = result .. "}"
  return result
end


function test (functionName, functionObj, testCases)
  for i, value in ipairs (testCases) do   
    if (functionObj(value[1])==value[2]) then
--      print ("OK!")
    else
      print ("Test "..i.." for "..functionName.." failed!".." Expected:"..value[2]..
	" Got:"..functionObj(value[1]))
    end
  end  
end

tabToStringTestCases={ 
   {{1,2,3},"{1,2,3}"}, 
   {{1,2,4},"{1,2,4}"},
   {{1,2,{4,5}},"{1,2,{4,5}}"},
   {{"&",A,B},"{&,A,B}"}
}

function allTests()
  test("tabToString", tabToString, tabToStringTestCases)
end


allTests()

----------
-- Rules for obtaining FNC 


-- 1. Implication rule: from A->B to !A|B

testFncImpRuleTestCases =
{ 
  { {IMP, A, B}, {OR, {NOT, A}, B} },
  { {IMP, B, A}, {OR, {NOT, B}, A} },
  { {AND, B, A}, {AND, B, A} },
  { {OR, B, A}, {OR, B, A} },
  { {NOT, B}, {NOT, B} },
  { {OR, {AND, B, "C"}, A}, {OR, {AND, B, "C"}, A} },

}

function fncImpRule (formula)
   if (type(formula)=="table") then
     if (formula[1]==IMP) then
        result={OR, {NOT, formula[2]}, formula[3]}
        return result
     else 
        return formula
     end
  end
end

function testRule(func, test_cases)
  for i, testCasePair in ipairs (test_cases) do
    print (tabToString(testCasePair[1]).." <-- Input")
    print (tabToString(func(testCasePair[1])).." <-- Result")
    print (tabToString(testCasePair[2]).." <-- Expected result")
    print()
  end
end

print("imp rule")

testRule(fncImpRule, testFncImpRuleTestCases)

print("-- imp rule\n")

-- 2. Double negation rule: from !!A to A

testFncNotNotRuleTestCases =
{ 
  { {NOT, {NOT, A}} , {A} },
  { {IMP, A, B}, {IMP, A, B} },
  { {OR, {NOT, B}, A}, {OR, {NOT, B}, A} },
}


function fncNotNotRule (formula)
   if (type(formula)=="table") and (formula[1]==NOT) and (type(formula[2])=="table") and (formula[2][1]==NOT) then
        result={formula[2][2]}
        return result
   else 
        return formula
   end
end

print("not not rule")

testRule(fncNotNotRule, testFncNotNotRuleTestCases)

print("-- not not rule\n")


-- 3.1 Negation internalization: from !(A&B) to !A|!B
-- 3.2. Negation internalization: from !(A|B) to !A&!B

testFncNegIntTestCases =
{ 
  { {NOT, {AND, A, B} } , {OR, {NOT, A}, {NOT, B}} },
  { {NOT, {OR, A, B} } , {AND, {NOT, A}, {NOT, B}} },
}


function fncNegInt (formula)
   local op
   if (type(formula)=="table") and (formula[1]==NOT) and (type(formula[2])=="table") and ((formula[2][1]==AND) or (formula[2][1]==OR)) then
        if (formula[2][1] == AND) then
            op = OR
        else
            op = AND
        end

        result={op, {NOT, formula[2][2]}, {NOT, formula[2][3]}}
        return result
   else 
        return formula
   end
end

print("neg int rule")

testRule(fncNegInt, testFncNegIntTestCases)

print("-- neg int rule\n")


-- 4.1. Distribution of & over |: from (A&(B|C)) to ((A&B)|(A&C))
-- 4.2. Distribution of & over |: from ((B|C)&A) to ((B&A)|(C&A))

testFncDistTestCases =
{ 
  { {AND, A, {OR, B, C} } , {OR, {AND, A, B}, {AND, A, C}} },
  { {AND, {OR, B, C}, A } , {OR, {AND, B, A}, {AND, C, A}} },
}


function fncDist (formula)
   if (type(formula)=="table") and (formula[1]==AND) and (type(formula[3])=="table") and (formula[3][1]==OR) then
        result={OR, {AND, formula[2], formula[3][2]}, {AND, formula[2], formula[3][3]}}
        return result
   else 
   	if (type(formula)=="table") and (formula[1]==AND) and (type(formula[2])=="table") and (formula[2][1]==OR) then
        	result={OR, {AND, formula[2][1], formula[3]}, {AND, formula[2][2], formula[3]}}
	        return result
	   else
        	return formula
	   end
   end
end

print("dist rule")

testRule(fncDist, testFncDistTestCases )

print("-- dist rule\n")


-- 5.1 Identifying  (A&(B&C)) with (A&B&C)
-- 5.2 Identifying   ((A&B)&C) with (A&B&C)
-- 5.3 Identifying   (A|(B|C)) with (A|B|C)
-- 5.4 Identifying   ((A|B)|C) with (A|B|C)

testFncAssTestCases =
{ 
  { {AND, A, {AND, B, C} } , {AND, A, B, C} },
  { {AND, {AND, A, B}, C } , {AND, A, B, C} },
  { {OR, A, {OR, B, C} } , {OR, A, B, C} },
  { {OR, {OR, A, B}, C } , {OR, A, B, C} },
}


function fncAss (formula)
	if (formula[1] == AND) or (formula[1] == OR) then
		local op = formula[1]

		if (type(formula[2]) == "table") and (formula[2][1] == op) then
			result={op, formula[2][2], formula[2][3], formula[3]}
		else
			if (type(formula[3]) == "table") and (formula[3][1] == op) then
				result={op, formula[2], formula[3][2], formula[3][3]}
			else
				return formula
			end
		end
		return result
	else
		return formula
	end
end

print("ass rule")

testRule(fncAss, testFncAssTestCases )

print("-- ass rule\n")

-- TODO
-- Iterate over rules 1-4 until no rule can be applied
-- What to do so that (A|(B|C))=((A|B)|C)=(A|B|C) and (A&(B&C))=((A&B)&C)=(A&B&C)
