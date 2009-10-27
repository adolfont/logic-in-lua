-- Normal Forms in Lua
-- Adolfo Neto (DAINF-UTFPR) http://www.dainf.ct.utfpr.edu.br/~adolfo
-- October 2009

-- Utilitary functions

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
   {{"&","A","B"},"{&,A,B}"}
}

function allTests()
  test("tabToString", tabToString, tabToStringTestCases)
end


allTests()

----------
-- Rules for obtaining FNC 

IMP="->"
AND="&"
OR="|"
NOT="!"

-- 1. Implication rule: from A->B to !A|B

testFncImpRuleTestCases =
{ 
  { {IMP, "A", "B"}, {OR, {NOT, "A"}, "B"} },
  { {IMP, "B", "A"}, {OR, {NOT, "B"}, "A"} },
  { {AND, "B", "A"}, {AND, "B", "A"} },
  { {OR, "B", "A"}, {OR, "B", "A"} },
  { {NOT, "B"}, {NOT, "B"} },
  { {OR, {AND, "B", "C"}, "A"}, {OR, {AND, "B", "C"}, "A"} },

}

function fncImpRule (formula)
   if (type(formula)=="table") then
     if (formula[1]==IMP) then
        result={OR, {NOT, formula[2], formula[3]}}
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

testRule(fncImpRule, testFncImpRuleTestCases)

-- 2. Double negation rule: from !!A to A

testFncNotNotRuleTestCases =
{ 
  { {NOT, {NOT, "A"}} , {"A"} },
  { {IMP, "A", "B"}, {IMP, "A", "B"} },
  { {OR, {NOT, "B"}, "A"}, {OR, {NOT, "B"}, "A"} },
}


function fncNotNotRule (formula)
   if (type(formula)=="table") and (formula[1]==NOT) and 
       (type(formula[2])=="table") and (formula[2][1]==NOT) then
        result={formula[2][2]}
        return result
     else 
        return formula
   end
end

testRule(fncNotNotRule, testFncNotNotRuleTestCases)

-- TODO
-- 3.1. Negation internalization: from !(A&B) to !A|!B
-- 3.2. Negation internalization: from !(A|B) to !A&!B
-- 4.1. Distribution of & over |: from (A&(B|C)) to ((A&B)|(A&C))
-- 4.2. Distribution of & over |: from ((B|C)&A) to ((B&A)|(C&A))
-- Iterate over rules 1-4 until no rule can be applied
-- What to do so that (A|(B|C))=((A|B)|C)=(A|B|C) and (A&(B&C))=((A&B)&C)=(A&B&C)
