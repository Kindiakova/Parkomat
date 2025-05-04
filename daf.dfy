
class Receipt{
    var startTime : int
    var duration : int

    constructor(startTime: int, duration: int)
        ensures this.startTime == startTime
        ensures this.duration == duration
    {
        this.startTime := startTime;
        this.duration := duration;
    }
}

class ParkingMeter {
    
    var receipts: map<string, seq<Receipt>> // Зберігає квитанції: номер транспорту -> список (час початку, тривалість)
    var totalEarnings: int // Загальна сума заробітку
    var ratePerHour: int // Тариф за годину

    constructor(rate: int)
        ensures ratePerHour == rate
        ensures totalEarnings == 0
        ensures receipts == map[]
    {
        ratePerHour := rate;
        totalEarnings := 0;
        receipts := map[];
        print"Паркометр iнiцiалiзовано з тарифом за годину: ", rate, "\n";
    }

    // Метод для видачі квитанції
    method IssueReceipt(terminalWorks : bool, vehicleNumber: string, duration: int, 
                        paymentType:string, amountPaid : int, currentTime : int)  returns (success: bool, ghost paymentSuccessful: bool)
        requires duration > 0
        requires amountPaid >= 0
        modifies this
        ensures paymentSuccessful ==> success
        ensures success ==> paymentSuccessful == true
        ensures success ==> vehicleNumber in this.receipts && exists t: 
                Receipt :: t in this.receipts[vehicleNumber] && t.startTime + t.duration > currentTime
    {
        print "Видача квитанцiї на паркування для транспорту: ", vehicleNumber, "\n";
        var paymentMade := AcceptPayment(terminalWorks, vehicleNumber, duration, paymentType, amountPaid, currentTime);

        assert (terminalWorks || paymentType !=  "card") && (amountPaid >= this.ratePerHour * duration) ==> paymentMade;

        paymentSuccessful := paymentMade;
        if (!paymentMade) {
            print "Оплата не прийнята для транспорту: ", vehicleNumber, "\n";
            var success := false;
            return success, paymentSuccessful;
        }

        assert paymentSuccessful == true;

        var newStartTime: int := currentTime;
        if vehicleNumber in this.receipts && |this.receipts[vehicleNumber]| > 0 {
            var lastReceipt := this.receipts[vehicleNumber][|this.receipts[vehicleNumber]| - 1];
            if lastReceipt.startTime + lastReceipt.duration > currentTime {
                newStartTime := lastReceipt.startTime + lastReceipt.duration;
                print "Корегуємо час початку для транспорту: ", vehicleNumber, " на ", newStartTime, "\n";
            }
        }
        var newReceipt := new Receipt(newStartTime, duration);
        print "Створена нова квитанцiя: \n";

        if (vehicleNumber in this.receipts) {
            this.receipts := this.receipts[vehicleNumber := this.receipts[vehicleNumber] + [newReceipt]];
            print "Додано квитанцiю для транспорту: ", vehicleNumber, "\n";
        } else {
            this.receipts :=  this.receipts[vehicleNumber := [newReceipt]];
            print "Створено квитанцiю для транспорту: ", vehicleNumber, "\n";
        }
        return true, paymentSuccessful;
    }

    // Метод для прийняття оплати
    method AcceptPayment(terminalWorks: bool, vehicleNumber: string, duration: int, 
                         paymentType: string, amountPaid: int, currentTime: int) returns (success: bool)
        requires duration > 0 
        requires amountPaid >= 0
        modifies this
        ensures (terminalWorks || paymentType !=  "card") && (amountPaid >= this.ratePerHour * duration) ==> success
        ensures success ==> totalEarnings >= old(totalEarnings) + this.ratePerHour * duration
    {
        print "Прийняття оплати для транспорту: ", vehicleNumber, "\n";

        if (!terminalWorks && paymentType == "card") {
            print "Термiнал не працює для оплати карткою.\n";
            return false;
        }
 
        var cost := this.ratePerHour * duration;
        if (amountPaid < cost) {
            print "Недостатня оплата для транспорту: ", vehicleNumber, "\n";
            return false;
        }
    
        this.totalEarnings := this.totalEarnings + amountPaid;
        print "Оплата прийнята. Загальнi заробiтки оновленi: ", this.totalEarnings, "\n";
        return true;
    }

    // Метод для перевірки, чи було сплачено
    method VerifyPayment(vehicleNumber: string, currentTime: int) returns (isPaid: bool)
        ensures isPaid ==> vehicleNumber in this.receipts && exists t: 
                Receipt :: t in this.receipts[vehicleNumber] && t.startTime + t.duration > currentTime
    {
        print "Перевiрка оплати для транспорту: ", vehicleNumber, "\n";  

        if vehicleNumber in this.receipts {
            var receiptsList := this.receipts[vehicleNumber];
            var n := |receiptsList|; 
            var i := 0;

            while i < n {
                var receipt := receiptsList[i];
                if receipt.startTime + receipt.duration > currentTime {
                    print "Знайдена дiйсна квитанцiя для транспорту: ", vehicleNumber, "\n";
                    return true;
                }
                i := i + 1;
            }
        }
        
        print "Дiйсна оплата не знайдена для транспорту: ", vehicleNumber, "\n";
        return false;
    }
}

method Main(){
    var rate := 10; // Тариф за годину
    var parkingMeter := new ParkingMeter(rate);

    // Видаємо квитанцію для транспорту
    var vehicleNumber := "AB1234CD";
    var duration := 2; // тривалість паркування в годинах
    var paymentType := "card"; // тип оплати
    var amountPaid := 20; // сума оплати
    var currentTime := 10; // поточний час (час початку паркування)

    // Демонстрація видачі квитанції
    print "Демо 1: Видача квитанцiї\n";
    var success, paymentSuccessful:= parkingMeter.IssueReceipt(true, vehicleNumber, duration, paymentType, amountPaid, currentTime);
    print"Квитанцiя видана?: ", success, "\n";

    assert paymentSuccessful ==> success;  

    // Перевіряємо оплату для транспорту
    print "\nДемо 2: Перевiрка оплати\n";
    var isPaid := parkingMeter.VerifyPayment(vehicleNumber, currentTime + 1); // Перевірка через 1 годину після початку
    print "Оплата пiдтверджена: ", isPaid, "\n";


    // Додаємо ще одну квитанцію для того ж транспорту
    print "\nДемо 3: Додавання нової квитанцiї\n";
    var newDuration := 3; // нова тривалість
    var newAmountPaid := 30; // нова сума оплати
    var newCurrentTime := currentTime + 1;
    var newPaymentType := "cash";
    var newSuccess, paymentSuccessful2 := parkingMeter.IssueReceipt(true, vehicleNumber, newDuration, newPaymentType, newAmountPaid, newCurrentTime);
    print "Нова квитанцiя видана?: ", newSuccess, "\n";

    assert paymentSuccessful ==> success;  

    // Перевіряємо оплату після додавання нової квитанції
    print "\nДемо 4: Перевiрка оплати пiсля додавання нової квитанцiї\n";
    var newIsPaid := parkingMeter.VerifyPayment(vehicleNumber, currentTime + 4); // Перевірка через 4 години після початку
    print "Оплата пiдтверджена для нової квитанцiї: ", newIsPaid, "\n";

    // Перевіряємо загальні заробіток
    print "\nДемо 5: Загальнi заробiток паркометра\n";
    print "Сума: ", parkingMeter.totalEarnings, "\n";
}
