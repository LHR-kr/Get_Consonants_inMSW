--@ BeginMethod
--@ MethodExecSpace=All
any utf8sub(any s,any i,any j)
{
-- argument defaults
	j = j or -1

	local pos = 1
	local bytes = string.len(s)
	local length = 0

	-- only set l if i or j is negative
	local l = (i >= 0 and j >= 0) or self:utf8len(s)
	local startChar = (i >= 0) and i or l + i + 1
	local endChar   = (j >= 0) and j or l + j + 1

	-- can't have start before end!
	if startChar > endChar then
		return ""
	end

	-- byte offsets to pass to string.sub
	local startByte,endByte = 1,bytes

	while pos <= bytes do
		length = length + 1

		if length == startChar then
			startByte = pos
		end

		pos = pos + self:utf8charbytes(s, pos)

		if length == endChar then
			endByte = pos - 1
			break
		end
	end

	if startChar > length then startByte = bytes+1   end
	if endChar   < 1      then endByte   = 0         end

	return string.sub(s, startByte, endByte)
}
--@ EndMethod

--@ BeginMethod
--@ MethodExecSpace=All
any utf8charbytes(any s,any i)
{
-- argument defaults
	i = i or 1

	-- argument checking
	if type(s) ~= "string" then
		error("bad argument #1 to 'utf8charbytes' (string expected, got ".. type(s).. ")")
	end
	if type(i) ~= "number" then
		error("bad argument #2 to 'utf8charbytes' (number expected, got ".. type(i).. ")")
	end

	local c = string.byte(s, i)

	-- determine bytes needed for character, based on RFC 3629
	-- validate byte 1
	if c > 0 and c <= 127 then
		-- UTF8-1
		return 1

	elseif c >= 194 and c <= 223 then
		-- UTF8-2
		local c2 = string.byte(s, i + 1)

		if not c2 then
			error("UTF-8 string terminated early")
		end

		-- validate byte 2
		if c2 < 128 or c2 > 191 then
			error("Invalid UTF-8 character")
		end

		return 2

	elseif c >= 224 and c <= 239 then
		-- UTF8-3
		local c2 = string.byte(s, i + 1)
		local c3 = string.byte(s, i + 2)

		if not c2 or not c3 then
			error("UTF-8 string terminated early")
		end

		-- validate byte 2
		if c == 224 and (c2 < 160 or c2 > 191) then
			error("Invalid UTF-8 character")
		elseif c == 237 and (c2 < 128 or c2 > 159) then
			error("Invalid UTF-8 character")
		elseif c2 < 128 or c2 > 191 then
			error("Invalid UTF-8 character")
		end

		-- validate byte 3
		if c3 < 128 or c3 > 191 then
			error("Invalid UTF-8 character")
		end

		return 3

	elseif c >= 240 and c <= 244 then
		-- UTF8-4
		local c2 = string.byte(s, i + 1)
		local c3 = string.byte(s, i + 2)
		local c4 = string.byte(s, i + 3)

		if not c2 or not c3 or not c4 then
			error("UTF-8 string terminated early")
		end

		-- validate byte 2
		if c == 240 and (c2 < 144 or c2 > 191) then
			error("Invalid UTF-8 character")
		elseif c == 244 and (c2 < 128 or c2 > 143) then
			error("Invalid UTF-8 character")
		elseif c2 < 128 or c2 > 191 then
			error("Invalid UTF-8 character")
		end

		-- validate byte 3
		if c3 < 128 or c3 > 191 then
			error("Invalid UTF-8 character")
		end

		-- validate byte 4
		if c4 < 128 or c4 > 191 then
			error("Invalid UTF-8 character")
		end

		return 4

	else
		error("Invalid UTF-8 character")
	end
}
--@ EndMethod

--@ BeginMethod
--@ MethodExecSpace=All
any utf8unicode(any str,any i,any j,any byte_pos)
{
local shift_6  = 2^6
local shift_12 = 2^12
local shift_18 = 2^18

i = i or 1
	j = j or i

	if i > j then return end

	local ch,bytes

	if byte_pos then
		bytes = self:utf8charbytes(str,byte_pos)
		ch  = string.sub(str,byte_pos,byte_pos-1+bytes)
	else
		ch,byte_pos = self:utf8sub(str,i,i), 0
		bytes       = #ch
	end

	local unicode

	if bytes == 1 then unicode = string.byte(ch) end
	if bytes == 2 then
		local byte0,byte1 = string.byte(ch,1,2)
		local code0,code1 = byte0-0xC0,byte1-0x80
		unicode = code0*shift_6 + code1
	end
	if bytes == 3 then
		local byte0,byte1,byte2 = string.byte(ch,1,3)
		local code0,code1,code2 = byte0-0xE0,byte1-0x80,byte2-0x80
		unicode = code0*shift_12 + code1*shift_6 + code2
	end
	if bytes == 4 then
		local byte0,byte1,byte2,byte3 = string.byte(ch,1,4)
		local code0,code1,code2,code3 = byte0-0xF0,byte1-0x80,byte2-0x80,byte3-0x80
		unicode = code0*shift_18 + code1*shift_12 + code2*shift_6 + code3
	end

	return unicode,self:utf8unicode(str, i+1, j, byte_pos+bytes)
}
--@ EndMethod

--@ BeginMethod
--@ MethodExecSpace=All
any utf8len(any s)
{
-- argument checking
	if type(s) ~= "string" then
		for k,v in pairs(s) do print('"',tostring(k),'"',tostring(v),'"') end
		error("bad argument #1 to 'utf8len' (string expected, got ".. type(s).. ")")
	end

	local pos = 1
	local bytes = string.len(s)
	local length = 0

	while pos <= bytes do
		length = length + 1
		pos = pos + self:utf8charbytes(s, pos)
	end

	return length
}
--@ EndMethod

--@ BeginMethod
--@ MethodExecSpace=All
any utf8char(any unicode)
{
if unicode <= 0x7F then return string.char(unicode) end

	if (unicode <= 0x7FF) then
		local Byte0 = 0xC0 + math.floor(unicode / 0x40);
		local Byte1 = 0x80 + (unicode % 0x40);
		return string.char(Byte0, Byte1);
	end;

	if (unicode <= 0xFFFF) then
		local Byte0 = 0xE0 +  math.floor(unicode / 0x1000);
		local Byte1 = 0x80 + (math.floor(unicode / 0x40) % 0x40);
		local Byte2 = 0x80 + (unicode % 0x40);
		return string.char(Byte0, Byte1, Byte2);
	end;

	if (unicode <= 0x10FFFF) then
		local code = unicode
		local Byte3= 0x80 + (code % 0x40);
		code       = math.floor(code / 0x40)
		local Byte2= 0x80 + (code % 0x40);
		code       = math.floor(code / 0x40)
		local Byte1= 0x80 + (code % 0x40);
		code       = math.floor(code / 0x40)
		local Byte0= 0xF0 + code;

		return string.char(Byte0, Byte1, Byte2, Byte3);
	end;

	error 'Unicode cannot be greater than U+10FFFF!'
}
--@ EndMethod

--@ BeginMethod
--@ MethodExecSpace=All
any GetKLua()
{
local chosungPairs = {["ㄱ"]=4352, ["ㄲ"]=4353, ["ㄴ"]=4354, ["ㄷ"]=4355, ["ㄸ"]=4356, ["ㄹ"]=4357, ["ㅁ"]=4358, ["ㅂ"]=4359, ["ㅃ"]=4360, ["ㅅ"]=4361, ["ㅆ"]=4362, ["ㅇ"]=4363, ["ㅈ"]=4364, ["ㅉ"]=4365, ["ㅊ"]=4366, ["ㅋ"]=4367, ["ㅌ"]=4368, ["ㅍ"]=4369, ["ㅎ"]=4370}
local jongsungPairs = {["ㄱ"]=4352, ["ㄲ"]=4353, ["ㄳ"]=4354, ["ㄴ"]=4355, ["ㄵ"]=4356, ["ㄶ"]=4357, ["ㄷ"]=4358, ["ㄹ"]=4359, ["ㄺ"]=4360, ["ㄻ"]=4361, ["ㄼ"]=4362, ["ㄽ"]=4363, ["ㄾ"]=4364, ["ㄿ"]=4365, ["ㅀ"]=4366, ["ㅁ"]=4367, ["ㅂ"]=4368, ["ㅄ"]=4369, ["ㅅ"]=4370, ["ㅆ"]=4371, ["ㅇ"]=4372, ["ㅈ"]=4373, ["ㅊ"]=4374, ["ㅋ"]=4375, ["ㅌ"]=4376, ["ㅍ"]=4377, ["ㅎ"]=4378}



local chosungs = {"ㄱ", "ㄲ", "ㄴ", "ㄷ", "ㄸ", "ㄹ", "ㅁ", "ㅂ", "ㅃ", "ㅅ", "ㅆ", "ㅇ", "ㅈ", "ㅉ", "ㅊ", "ㅋ", "ㅌ", "ㅍ", "ㅎ"}
local i_jaums = {"ㄱ", "ㄲ", "ㄴ", "ㄷ", "ㄸ", "ㄹ", "ㅁ", "ㅂ", "ㅃ", "ㅅ", "ㅆ", "ㅇ", "ㅈ", "ㅉ", "ㅊ", "ㅋ", "ㅌ", "ㅍ", "ㅎ"}
local i_jaums_jongsung = {"ㄱ","ㄲ","ㄳ","ㄴ","ㄵ","ㄶ","ㄷ","ㄹ","ㄺ","ㄻ","ㄼ","ㄽ","ㄾ","ㄿ","ㅀ","ㅁ","ㅂ","ㅄ","ㅅ","ㅆ","ㅇ","ㅈ","ㅊ","ㅋ","ㅌ","ㅍ","ㅎ"}
local i_moums = {"ㅏ","ㅐ","ㅑ","ㅒ","ㅓ","ㅔ","ㅕ","ㅖ","ㅗ","ㅘ","ㅙ","ㅚ","ㅛ","ㅜ","ㅝ","ㅞ","ㅟ","ㅠ","ㅡ","ㅢ","ㅣ"}

for k,v in pairs(chosungs) do
    chosungs[v] = k
end
for k,v in ipairs(chosungs) do
    chosungs[k] = nil
end



local split = function(origStr)
    local returnTable = {}
    for ik = 1, utf8.len(origStr), 1 do
        local bytedStr = self:utf8unicode(self:utf8sub(origStr, ik, ik))
        if bytedStr >= self:utf8unicode("ㄱ") and bytedStr <= self:utf8unicode("힣") then
            local indexFirst = math.floor(((((bytedStr-44032) - (bytedStr-44032)%28))/28) / 21) + 1
            local indexSecond = math.floor(((((bytedStr-44032) - (bytedStr-44032)%28))/28) % 21) + 1
            local indexThird = math.floor((bytedStr-44032) % 28)
    
            if i_jaums[indexFirst] == nil then
                returnTable[#returnTable+1] = {utf8.char(bytedStr)}
            elseif indexThird == 0 then
                returnTable[#returnTable+1] = {i_jaums[indexFirst], i_moums[indexSecond]}
            else
                returnTable[#returnTable+1] = {i_jaums[indexFirst], i_moums[indexSecond], i_jaums_jongsung[indexThird]}
            end
        else
            returnTable[#returnTable+1] = {utf8.char(bytedStr)}
        end
    end
    return returnTable
end

local returnTable = {}
for k,v in pairs(utf8) do
    returnTable[k] = v
end
returnTable.split = split

return returnTable
}
--@ EndMethod

--@ BeginMethod
--@ MethodExecSpace=All
table GetConsonants(string str)
{
local KLua = self:GetKLua()

local consonantTable = KLua.split(str)

local rtntable = {}

for i,v in ipairs(consonantTable) do
	rtntable[i]=v[1]
end
return rtntable

}
--@ EndMethod

