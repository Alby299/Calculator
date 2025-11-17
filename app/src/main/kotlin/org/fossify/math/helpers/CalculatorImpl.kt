package org.fossify.math.helpers

import android.content.Context
import android.widget.Toast
import androidx.compose.material3.rememberRangeSliderState
import com.ezylang.evalex.Expression
import kotlinx.coroutines.channels.Channel
import org.fossify.commons.extensions.showErrorToast
import org.fossify.commons.extensions.toInt
import org.fossify.commons.extensions.toast
import org.fossify.math.R
import org.fossify.math.models.History
import org.json.JSONObject
import org.json.JSONTokener
import java.math.BigDecimal
import java.math.BigInteger
import kotlin.enums.enumEntries
import kotlin.math.E
import kotlin.math.PI
import kotlin.math.abs  
import kotlin.math.absoluteValue
import kotlin.math.acos
import kotlin.math.asin
import kotlin.math.atan
import kotlin.math.cos
import kotlin.math.ln
import kotlin.math.log10
import kotlin.math.pow
import kotlin.math.sin
import kotlin.math.sqrt
import kotlin.math.tan
import kotlin.text.Regex

class CalculatorImpl(
    calculator: Calculator,
    private val context: Context,
    calculatorState: String = ""
) {
    private var callback: Calculator? = calculator
    private var stateInstance = calculatorState
    private var currentResult = "0"
    private var previousCalculation = ""
    private var baseValue = BigDecimal.ZERO
    private var secondValue = BigDecimal.ZERO
    private var inputDisplayedFormula = "0"
    private var lastKey = ""
    private var lastOperation = ""
    private val operations = listOf("+", "-", "×", "÷", "^", "%", "√")

    private val unitaryFncOperations = listOf("√", "log", "ln", "sin", "cos", "tan", "sin⁻¹", "cos⁻¹", "tan⁻¹", "!")
    private val binaryOperationsHighPriority = listOf("^")
    private val binaryOperationsMidPriority = listOf("×", "÷")
    private val binaryOperationsLowPriority = listOf("+", "-")
    private val constantSymbol = listOf("π", "e")

    // - \d+(\.\d+)? : Numbers
    // - [a-z⁻¹]+ : Function
    // - [+\-×√÷%^()] : Operators and Brackets
    private val tokenRegex = Regex("(\\d+(\\.\\d+)?)|([a-z⁻¹]+)|([+\\-×√÷%^()!π])")

    private val operationsRegex = "[-+×÷^%√]".toPattern()
    private val formatter = NumberFormatHelper()

    private val decimalSeparator: String get() = formatter.decimalSeparator
    private val groupingSeparator: String get() = formatter.groupingSeparator
    private val numbersRegex: Regex get() =
        "[^0-9${Regex.escape(decimalSeparator)}${Regex.escape(groupingSeparator)}]".toRegex()

    var useDeg = false;
    private val maxResultLength = 15

    init {
        if (stateInstance != "") {
            setFromSaveInstanceState(stateInstance)
        }
        showNewResult(currentResult)
        showNewFormula(previousCalculation)
    }

    private fun addDigit(number: Int) {
        if (inputDisplayedFormula == "0") {
            inputDisplayedFormula = ""
        }

        inputDisplayedFormula += number
        addThousandsDelimiter()
        showNewResult(inputDisplayedFormula)
    }

    private fun zeroClicked() {
        val valueToCheck = inputDisplayedFormula.trimStart('-').removeGroupSeparator()
        val value = valueToCheck.substring(valueToCheck.indexOfAny(operations) + 1)
        if (value != "0" || value.contains(decimalSeparator)) {
            addDigit(0)
        }
    }

    private fun decimalClicked() {
        val valueToCheck = inputDisplayedFormula.trimStart('-').replace(groupingSeparator, "")
        val value = valueToCheck.substring(valueToCheck.indexOfAny(operations) + 1)
        if (!value.contains(decimalSeparator)) {
            when {
                value == "0" && !valueToCheck.contains(operationsRegex.toRegex()) -> {
                    inputDisplayedFormula = "0$decimalSeparator"
                }

                value == "" -> inputDisplayedFormula += "0$decimalSeparator"
                else -> inputDisplayedFormula += decimalSeparator
            }
        }

        lastKey = DECIMAL
        showNewResult(inputDisplayedFormula)
    }

    private fun addThousandsDelimiter() {
        val valuesToCheck = numbersRegex.split(inputDisplayedFormula)
            .filter { it.trim().isNotEmpty() }
        valuesToCheck.forEach {
            val formatted = formatter.formatForDisplay(it)
            inputDisplayedFormula = inputDisplayedFormula.replace(it, formatted)
        }
    }

    fun handleOperation(operation: String) {
        if (inputDisplayedFormula == "0") {
            inputDisplayedFormula = ""
        }
        inputDisplayedFormula += getSign(operation)

        showNewResult(inputDisplayedFormula)
    }

    fun handleEquals() {
        val result = calculateResult()
        if (result != null) {
            val formattedString = result.format()
            showNewResult(formattedString)
            HistoryHelper(context).insertOrUpdateHistoryEntry(
                History(
                    id = null,
                    formula = inputDisplayedFormula,
                    result = formattedString,
                    timestamp = System.currentTimeMillis()
                )
            )
            showNewFormula(inputDisplayedFormula)
            inputDisplayedFormula = result.format()
        }
    }

    private fun operationWeight(op: String): Int {
        return when (op) {
            in unitaryFncOperations -> 4
            in binaryOperationsHighPriority -> 3
            in binaryOperationsMidPriority -> 2
            in binaryOperationsLowPriority -> 1
            else -> 0
        }
    }

    private fun tokenizeInput(): List<String> {

        val formattedInput = inputDisplayedFormula
            .replace(".", "")
            .replace(",", ".")
        val tokens = tokenRegex.findAll(formattedInput)
            .map { it.value }
            .toMutableList()

        val finalTokens = mutableListOf<String>()
        var i = 0
        while (i < tokens.size) {
            val token = tokens[i]

            if (token == "-") {
                val isUnary = i == 0 || tokens[i - 1] in
                    binaryOperationsHighPriority + binaryOperationsMidPriority + binaryOperationsLowPriority + "("

                if (isUnary) {
                    if (i + 1 < tokens.size &&
                        (tokens[i + 1].toDoubleOrNull() != null || tokens[i + 1] in constantSymbol)) {
                        finalTokens.add("-" + tokens[i + 1])
                        i += 2
                        continue
                    }
                }
            }
            if (token in constantSymbol + "("){
                val hasCoefficient = i != 0 && tokens[i - 1].toDoubleOrNull() != null
                if (hasCoefficient) finalTokens.add("×")
            }
            finalTokens.add(token)
            i++
        }

        return finalTokens
    }

    private fun parseRPN(): List<String>? {
        val tokenList = tokenizeInput()
        val operatorStack = mutableListOf<String>()
        val outputQueue = mutableListOf<String>()

        for (token in tokenList) {
            when {
                token.toDoubleOrNull() != null -> {
                    outputQueue.add(token)
                }
                token in constantSymbol + constantSymbol.map { "-$it" } -> {
                    outputQueue.add(token)
                }

                token in unitaryFncOperations -> {
                    operatorStack.add(token)
                }

                token == "(" -> {
                    operatorStack.add(token)
                }

                token == ")" -> {
                    while (operatorStack.isNotEmpty() && operatorStack.last() != "(") {
                        outputQueue.add(operatorStack.removeAt(operatorStack.lastIndex))
                    }

                    if (operatorStack.isNotEmpty() && operatorStack.last() == "(") {
                        operatorStack.removeAt(operatorStack.lastIndex)
                    } else {
                        context.showErrorToast("Unbalanced Brackets", Toast.LENGTH_LONG)
                        return null
                    }

                    if (operatorStack.isNotEmpty() && operationWeight(operatorStack.last()) == 4) {
                        outputQueue.add(operatorStack.removeAt(operatorStack.lastIndex))
                    }
                }

                operationWeight(token) > 0 -> {
                    val currentLastOperation = operationWeight(token)

                    while (operatorStack.isNotEmpty() && operationWeight(operatorStack.last()) >= currentLastOperation) {
                        if (operatorStack.last() == "(") break

                        outputQueue.add(operatorStack.removeAt(operatorStack.lastIndex))
                    }
                    operatorStack.add(token)
                }
            }
        }

        while (operatorStack.isNotEmpty()) {
            val op = operatorStack.removeAt(operatorStack.lastIndex)
            if (op == "(" || op == ")") {
                context.showErrorToast("Unbalanced brackets", Toast.LENGTH_LONG)
                return null
            }
            outputQueue.add(op)
        }

        return outputQueue
    }
    //TODO: add Scientific Notation
    //TODO: Correct Stack Overflow of displayFormula
    private fun calculateResult(): BigDecimal? {
        if (parseRPN() == null) return null

        val rpnTokens = parseRPN()
        val stack = mutableListOf<BigDecimal>()

        for(token in rpnTokens!!){
            when {
                token.toBigDecimalOrNull() != null -> {
                    stack.add(token.toBigDecimal())
                }

                token in constantSymbol + constantSymbol.map { "-$it" } -> {
                    val isNegative = token.startsWith("-")
                    val baseToken = if (isNegative) token.substring(1) else token
                    val cValue : BigDecimal = when (baseToken) {
                        "π" -> PI.toBigDecimal()
                        "e" -> E.toBigDecimal()
                        else -> {
                            context.showErrorToast("Constant not implemented [$token]", Toast.LENGTH_LONG)
                            return null
                        }
                    }
                    val result = if (isNegative) cValue.negate() else cValue
                    stack.add(result)
                }

                token in binaryOperationsHighPriority + binaryOperationsMidPriority + binaryOperationsLowPriority -> {
                    if (stack.size < 2) {
                        context.showErrorToast("Insufficient operands [$token]", Toast.LENGTH_LONG)
                        return null
                    }

                    val operand2 = stack.removeAt(stack.lastIndex)
                    val operand1 = stack.removeAt(stack.lastIndex)

                    val result : BigDecimal? = when (token) {
                        "+" -> operand1 + operand2
                        "-" -> operand1 - operand2
                        "×" -> operand1 * operand2
                        "÷" -> handleDivision(operand1, operand2)
                        "^" -> handlePow(operand1, operand2)
                        else -> {
                            context.showErrorToast("Operand not implemented [$token]", Toast.LENGTH_LONG)
                            return null
                        }
                    }
                    if (result == null) {
                        context.showErrorToast("Invalid input [$token]", Toast.LENGTH_LONG)
                        return null
                    }
                    stack.add(result)
                }

                token in unitaryFncOperations -> {
                    if (stack.isEmpty()) {
                        context.showErrorToast("Insufficient operands [$token]", Toast.LENGTH_LONG)
                        return null
                    }

                    val operand = stack.removeAt(stack.lastIndex)

                    val result : BigDecimal? = when (token) {
                        "sin"   -> handleSin(operand)
                        "cos"   -> handleCos(operand)
                        "tan"   -> handleTan(operand)
                        "sin⁻¹" -> handleAsin(operand)
                        "cos⁻¹" -> handleAcos(operand)
                        "tan⁻¹" -> handleAtan(operand)
                        "log"   -> handleLog10(operand)
                        "ln"    -> handleLn(operand)
                        "√"     -> handleSqrt(operand)
                        "!"     -> handleFactorial(operand)
                        else -> {
                            context.showErrorToast("Function not implemented [$token]", Toast.LENGTH_LONG)
                            return null
                        }
                    }
                    if (result == null) {
                        context.showErrorToast("Invalid input [$token]", Toast.LENGTH_LONG)
                        return null
                    }
                    stack.add(result)
                }

                else -> {
                    context.showErrorToast("Invalid token ($token)", Toast.LENGTH_LONG)
                    return null
                }
            }
        }

        if (stack.size != 1) {
            context.showErrorToast("Wrong syntax", Toast.LENGTH_LONG)
            return null
        }

        return stack.single()
    }

    private fun handleDivision(a: BigDecimal, b: BigDecimal): BigDecimal?{
        if(b.equals(0)) return null
        return a.divide(b, MATH_CONTEXT)
    }
    private fun handleFactorial(x: BigDecimal): BigDecimal? {
        val n: Int
        try {
            n = x.intValueExact()
        } catch (_: ArithmeticException) {
            return null
        }

        return when {
            n < 0 -> null
            n == 0 -> BigDecimal.ONE
            else -> {
                (2..n)
                    .map { it.toBigInteger() }
                    .reduce { acc, bigInt -> acc.multiply(bigInt) }
                    .toBigDecimal()
            }
        }
    }
    private fun handleSqrt(x: BigDecimal): BigDecimal? {
        val n = x.toDouble()
        if (n < 0) return null
        return sqrt(n).toBigDecimal()
    }
    private fun handleLn(x: BigDecimal): BigDecimal? {
        val n = x.toDouble()
        if (n <= 0) return null
        return ln(n).toBigDecimal()
    }
    private fun handleLog10(x: BigDecimal): BigDecimal? {
        val n = x.toDouble()
        if (n <= 0) return null
        return log10(n).toBigDecimal()
    }
    private fun handleSin(x: BigDecimal): BigDecimal? {
        val value = x.toDouble()
        val n = if (!useDeg) value else value * PI / 180.0
        return sin(n).toBigDecimal()
    }
    private fun handleCos(x: BigDecimal): BigDecimal? {
        val value = x.toDouble()
        val n = if (!useDeg) value else value * PI / 180.0
        return cos(n).toBigDecimal()
    }
    private fun handleTan(x: BigDecimal): BigDecimal? {
        val value = x.toDouble()
        val n = if (!useDeg) value else value * PI / 180.0
        return tan(n).toBigDecimal()
    }
    private fun handleAsin(x: BigDecimal): BigDecimal? {
        val n = x.toDouble()
        if(n.absoluteValue > 1) return null
        val m = if (!useDeg) 1.0 else (180.0 / PI)
        return (asin(n) * m).toBigDecimal()
    }
    private fun handleAcos(x: BigDecimal): BigDecimal? {
        val n = x.toDouble()
        if(abs(n) > 1) return null
        val m = if (!useDeg) 1.0 else (180.0 / PI)
        return (acos(n) * m).toBigDecimal()
    }
    private fun handleAtan(x: BigDecimal): BigDecimal? {
        val n = x.toDouble()
        val m = if (!useDeg) 1.0 else (180.0 / PI)
        return (atan(n) * m).toBigDecimal()
    }
    private fun handlePow(base: BigDecimal, exponent: BigDecimal): BigDecimal? {
        try {
            val n = exponent.intValueExact()
            return base.pow(n, MATH_CONTEXT)
        } catch (_: ArithmeticException) {
            return base.toDouble().pow(exponent.toDouble()).toBigDecimal()
        }
    }

    private fun showNewResult(value: String) {
        currentResult = value
        callback!!.showNewResult(value, context)
    }

    private fun showNewFormula(value: String) {
        previousCalculation = value
        callback!!.showNewFormula(value, context)
    }

    fun handleClear() {
        val tokenFormula = tokenizeInput()
        val lastToken = tokenFormula.last()
        var newValue =
            if (lastToken.toBigDecimalOrNull() != null)
                inputDisplayedFormula.dropLast(1)
            else
                tokenFormula.dropLast(1).joinToString("").replace(".",",")

        if (newValue == "" || newValue == "0") {
            newValue = "0"
            lastKey = CLEAR
        }

        inputDisplayedFormula = newValue
        addThousandsDelimiter()
        showNewResult(inputDisplayedFormula)
    }

    fun handleReset() {
        resetValues()
        showNewResult("0")
        showNewFormula("")
        inputDisplayedFormula = ""
    }

    private fun resetValues() {
        baseValue = BigDecimal.ZERO
        secondValue = BigDecimal.ZERO
        lastKey = ""
        lastOperation = ""
    }

    private fun getSign(lastOperation: String) = when (lastOperation) {
        MINUS -> "-"
        MULTIPLY -> "×"
        DIVIDE -> "÷"
        PERCENT -> "%"
        POWER -> "^"
        ROOT -> "√"
        LOG -> "log("
        LN -> "ln("
        OPEN_BRACKET -> "("
        CLOSE_BRACKET -> ")"
        SIN -> "sin("
        COS -> "cos("
        TAN -> "tan("
        ARCSIN -> "sin⁻¹("
        ARCCOS -> "cos⁻¹("
        ARCTAN -> "tan⁻¹("
        FACTORIAL -> "!"
        PI_NUM -> "π"
        NEPERO_NUM -> "e"
        else -> "+"
    }

    fun numpadClicked(id: Int) {
        if (inputDisplayedFormula == "NaN") {
            inputDisplayedFormula = ""
        }

        if (lastKey == EQUALS) {
            lastOperation = EQUALS
        }

        lastKey = DIGIT

        when (id) {
            R.id.btn_decimal -> decimalClicked()
            R.id.btn_0 -> zeroClicked()
            R.id.btn_1 -> addDigit(1)
            R.id.btn_2 -> addDigit(2)
            R.id.btn_3 -> addDigit(3)
            R.id.btn_4 -> addDigit(4)
            R.id.btn_5 -> addDigit(5)
            R.id.btn_6 -> addDigit(6)
            R.id.btn_7 -> addDigit(7)
            R.id.btn_8 -> addDigit(8)
            R.id.btn_9 -> addDigit(9)
        }
    }

    fun addNumberToFormula(number: String) {
        handleReset()
        inputDisplayedFormula = number
        addThousandsDelimiter()
        showNewResult(inputDisplayedFormula)
    }

    private fun BigDecimal.format() = formatter.bigDecimalToString(this)

    private fun String.removeGroupSeparator() = formatter.removeGroupingSeparator(this)

    //TODO: understand this 2 fun
    fun getCalculatorStateJson(): JSONObject {
        val jsonObj = JSONObject()
        jsonObj.put(RES, currentResult)
        jsonObj.put(PREVIOUS_CALCULATION, previousCalculation)
        jsonObj.put(LAST_KEY, lastKey)
        jsonObj.put(LAST_OPERATION, lastOperation)
        jsonObj.put(BASE_VALUE, baseValue.toString())
        jsonObj.put(SECOND_VALUE, secondValue.toString())
        jsonObj.put(INPUT_DISPLAYED_FORMULA, inputDisplayedFormula)
        return jsonObj
    }

    private fun setFromSaveInstanceState(json: String) {
        val jsonObject = JSONTokener(json).nextValue() as JSONObject
        currentResult = jsonObject.getString(RES)
        previousCalculation = jsonObject.getString(PREVIOUS_CALCULATION)
        lastKey = jsonObject.getString(LAST_KEY)
        lastOperation = jsonObject.getString(LAST_OPERATION)
        baseValue = try {
            BigDecimal(jsonObject.getString(BASE_VALUE))
        } catch (_: Exception) {
            BigDecimal.ZERO
        }
        secondValue = try {
            BigDecimal(jsonObject.getString(SECOND_VALUE))
        } catch (_: Exception) {
            BigDecimal.ZERO
        }
        inputDisplayedFormula = jsonObject.getString(INPUT_DISPLAYED_FORMULA)
    }
}
