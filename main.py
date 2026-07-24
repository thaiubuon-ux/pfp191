import csv
import json
import math
import os
import sys
import unittest
import hashlib
import time
from datetime import datetime, timedelta

# -------------------- Cấu hình --------------------
DATA_FILE = "spms_data.json"
CSV_FILE = "spms_export.csv"
REPORT_FILE = "revenue_report_{period}.csv"

NOTIFY_OCCUPANCY_PCT = 90
OVERDUE_HOURS = 24
MAX_OCCUPANCY_LOG = 1000

# Mật khẩu mặc định (sẽ được băm khi lưu)
DEFAULT_ROOT_USER = "rootadmin"
DEFAULT_ROOT_PASSWORD = os.environ.get("ROOT_ADMIN_PASSWORD", "root123")
DEFAULT_ADMIN_USER = "admin"
DEFAULT_ADMIN_PASSWORD = os.environ.get("ADMIN_PASSWORD", "admin123")
DEFAULT_ATTENDANT_USER = "attendant"
DEFAULT_ATTENDANT_PASSWORD = "attendant123"
DEFAULT_OWNER_USER = "owner"
DEFAULT_OWNER_PASSWORD = "owner123"

# Các trạng thái tài khoản
STATUS_ACTIVE = "active"
STATUS_PENDING = "pending"
STATUS_REJECTED = "rejected"

# Vai trò cần Admin gốc (root) duyệt trước khi được phép đăng nhập
ROLES_REQUIRE_APPROVAL = ("admin", "attendant")

# -------------------- Hàm tiện ích --------------------
def _require_non_blank(value, field_name):
    if value is None or not str(value).strip():
        print(f"{field_name} cannot be empty.")
        return None
    return str(value).strip()

def hash_password(password, salt=None):
    """Băm mật khẩu với salt (nếu không có thì tạo mới)."""
    if salt is None:
        salt = os.urandom(16).hex()
    salted = salt + password
    hashed = hashlib.sha256(salted.encode()).hexdigest()
    return salt, hashed

def verify_password(password, salt, hashed):
    """Kiểm tra mật khẩu với salt và hash đã lưu."""
    _, new_hash = hash_password(password, salt)
    return new_hash == hashed

# -------------------- Các lớp mô hình --------------------
class ParkingSlot:
    def __init__(self, slot_id, is_available=True, plate=None, check_in=None, reserved_for=None):
        self.slot_id = slot_id
        self.is_available = is_available
        self.plate = plate
        self.check_in = check_in
        self.reserved_for = reserved_for

    def to_dict(self):
        return self.__dict__

    @staticmethod
    def from_dict(d):
        return ParkingSlot(**d)

    def __repr__(self):
        state = "occupied" if not self.is_available else ("reserved" if self.reserved_for else "free")
        return f"<Slot {self.slot_id} [{state}]>"

class Vehicle:
    def __init__(self, plate, first_seen=None, visit_count=0):
        self.plate = plate
        self.first_seen = first_seen or datetime.now().isoformat()
        self.visit_count = visit_count

    def to_dict(self):
        return self.__dict__

    @staticmethod
    def from_dict(d):
        return Vehicle(**d)

class Transaction:
    def __init__(self, plate, slot_id, check_in, check_out, fee, paid=False):
        self.plate = plate
        self.slot_id = slot_id
        self.check_in = check_in
        self.check_out = check_out
        self.fee = fee
        self.paid = paid

    def to_dict(self):
        return self.__dict__

    @staticmethod
    def from_dict(d):
        return Transaction(**d)

# -------------------- Lớp chính ParkingLot --------------------
class ParkingLot:
    """Quản lý toàn bộ bãi đỗ xe, bao gồm slot, xe, giao dịch và báo cáo."""

    def __init__(self, hourly_rate=10000):
        self.hourly_rate = hourly_rate

        # Dữ liệu người dùng: {username: {salt, hashed, role}}
        self.users = {}
        self._init_default_users()

        self.slots = {}
        self.vehicles = {}
        self.transactions = []
        self.occupancy_log = []

        self.load_data()

    def _init_default_users(self):
        """Tạo tài khoản mặc định (chỉ khi chưa tồn tại). Tất cả tài khoản mặc định
        đều ở trạng thái 'active' (kể cả admin/attendant mặc định), vì đây là các
        tài khoản khởi tạo hệ thống, không đi qua luồng đăng ký thông thường."""
        defaults = {
            DEFAULT_ROOT_USER: (DEFAULT_ROOT_PASSWORD, "root"),
            DEFAULT_ADMIN_USER: (DEFAULT_ADMIN_PASSWORD, "admin"),
            DEFAULT_ATTENDANT_USER: (DEFAULT_ATTENDANT_PASSWORD, "attendant"),
            DEFAULT_OWNER_USER: (DEFAULT_OWNER_PASSWORD, "owner"),
        }
        for user, (pw, role) in defaults.items():
            if user not in self.users:
                salt, hashed = hash_password(pw)
                self.users[user] = {
                    "salt": salt,
                    "hashed": hashed,
                    "role": role,
                    "status": STATUS_ACTIVE,
                }

    # ---------- Đăng ký tài khoản mới ----------
    def register_user(self, username, password, role):
        """Đăng ký tài khoản mới.

        - role == "owner": kích hoạt (active) ngay lập tức, đăng nhập được luôn.
        - role in ("admin", "attendant"): tạo với trạng thái 'pending', phải chờ
          Admin gốc (root) duyệt (approve_user) mới đăng nhập được.
        """
        username = _require_non_blank(username, "Username")
        if username is None:
            return False
        if username in self.users:
            print("Username đã tồn tại. Vui lòng chọn tên khác.")
            return False
        password = _require_non_blank(password, "Password")
        if password is None:
            return False
        if role not in ("admin", "attendant", "owner"):
            print("Vai trò không hợp lệ.")
            return False

        status = STATUS_PENDING if role in ROLES_REQUIRE_APPROVAL else STATUS_ACTIVE
        salt, hashed = hash_password(password)
        self.users[username] = {
            "salt": salt,
            "hashed": hashed,
            "role": role,
            "status": status,
        }
        self.save_data()

        if status == STATUS_PENDING:
            print(f"Đăng ký thành công! Tài khoản '{username}' (vai trò: {role}) "
                  f"đang chờ Admin gốc duyệt trước khi có thể đăng nhập.")
        else:
            print(f"Đăng ký thành công! Bạn có thể đăng nhập ngay với tài khoản '{username}'.")
        return True

    def pending_users(self):
        """Danh sách (username, role) đang chờ Admin gốc duyệt."""
        return [(u, info["role"]) for u, info in self.users.items()
                if info.get("status") == STATUS_PENDING]

    def list_users(self):
        """Danh sách toàn bộ tài khoản với role/trạng thái (không lộ mật khẩu)."""
        return [(u, info["role"], info.get("status", STATUS_ACTIVE))
                for u, info in self.users.items()]

    def approve_user(self, username):
        """Admin gốc duyệt một tài khoản admin/attendant đang chờ duyệt."""
        user = self.users.get(username)
        if not user:
            print("Không tìm thấy tài khoản.")
            return False
        if user.get("status") != STATUS_PENDING:
            print("Tài khoản này không ở trạng thái chờ duyệt.")
            return False
        user["status"] = STATUS_ACTIVE
        self.save_data()
        print(f"Đã duyệt tài khoản '{username}' (vai trò: {user['role']}). Có thể đăng nhập ngay.")
        return True

    def reject_user(self, username):
        """Admin gốc từ chối một tài khoản admin/attendant đang chờ duyệt."""
        user = self.users.get(username)
        if not user:
            print("Không tìm thấy tài khoản.")
            return False
        if user.get("status") != STATUS_PENDING:
            print("Tài khoản này không ở trạng thái chờ duyệt.")
            return False
        user["status"] = STATUS_REJECTED
        self.save_data()
        print(f"Đã từ chối tài khoản '{username}'.")
        return True

    # ---------- Xác thực ----------
    def authenticate(self, username, password):
        """Xác thực người dùng, trả về role hoặc None nếu thất bại.

        Nếu tài khoản đang chờ duyệt hoặc đã bị từ chối, đăng nhập sẽ bị từ chối
        kèm thông báo tương ứng, dù mật khẩu đúng.
        """
        user = self.users.get(username)
        if not user:
            return None
        if not verify_password(password, user["salt"], user["hashed"]):
            return None
        status = user.get("status", STATUS_ACTIVE)
        if status == STATUS_PENDING:
            print("Tài khoản của bạn đang chờ Admin gốc duyệt. Vui lòng quay lại sau.")
            return None
        if status == STATUS_REJECTED:
            print("Tài khoản của bạn đã bị Admin gốc từ chối. Vui lòng liên hệ quản trị viên.")
            return None
        return user["role"]

    def change_password(self, username, old_password, new_password):
        """Thay đổi mật khẩu cho một user."""
        if not self.authenticate(username, old_password):
            print("Sai mật khẩu hiện tại.")
            return False
        new_password = _require_non_blank(new_password, "Mật khẩu mới")
        if new_password is None:
            return False
        salt, hashed = hash_password(new_password)
        self.users[username]["salt"] = salt
        self.users[username]["hashed"] = hashed
        self.save_data()
        print("Mật khẩu đã được cập nhật.")
        return True

    # ---------- Cấu hình bãi ----------
    def configure_lot(self, total_slots, hourly_rate):
        if total_slots < 0 or hourly_rate < 0:
            print("Số slot và giá phải không âm.")
            return
        self.hourly_rate = hourly_rate

        # Thêm slot mới
        for i in range(1, total_slots + 1):
            slot_id = f"P{i}"
            if slot_id not in self.slots:
                self.slots[slot_id] = ParkingSlot(slot_id)

        # Xóa slot thừa (chỉ khi trống và không được đặt trước)
        extra_ids = sorted(
            [sid for sid in self.slots if sid.startswith("P") and sid[1:].isdigit()
             and int(sid[1:]) > total_slots],
            key=lambda sid: int(sid[1:]),
            reverse=True,
        )
        skipped = []
        for sid in extra_ids:
            slot = self.slots[sid]
            if slot.is_available and not slot.reserved_for:
                del self.slots[sid]
            else:
                skipped.append(sid)

        if skipped:
            print(f"Warning: không thể xóa {len(skipped)} slot đang bị chiếm/đặt trước.")
        self.save_data()

    def add_slot(self, slot_id):
        slot_id = _require_non_blank(slot_id, "Slot ID")
        if slot_id is None:
            return
        if slot_id in self.slots:
            print("Slot đã tồn tại!")
            return
        self.slots[slot_id] = ParkingSlot(slot_id)
        self.save_data()
        print(f"Slot {slot_id} đã được thêm.")

    def update_slot(self, slot_id, new_slot_id=None, is_available=None):
        if slot_id not in self.slots:
            print("Không tìm thấy slot.")
            return
        slot = self.slots[slot_id]
        if is_available is not None:
            slot.is_available = is_available
            if is_available:
                slot.plate = None
                slot.check_in = None
        if new_slot_id and new_slot_id != slot_id:
            new_slot_id = _require_non_blank(new_slot_id, "New slot ID")
            if new_slot_id is None:
                return
            if new_slot_id in self.slots:
                print("ID slot mới đã tồn tại.")
                return
            slot.slot_id = new_slot_id
            del self.slots[slot_id]
            self.slots[new_slot_id] = slot
        self.save_data()
        print("Slot đã được cập nhật.")

    def remove_slot(self, slot_id):
        slot = self.slots.get(slot_id)
        if not slot:
            print("Slot không tồn tại.")
            return
        if not slot.is_available:
            print("Không thể xóa: slot đang có xe.")
            return
        if slot.reserved_for:
            print(f"Không thể xóa: slot đang được đặt trước cho {slot.reserved_for}.")
            return
        del self.slots[slot_id]
        self.save_data()
        print(f"Slot {slot_id} đã bị xóa.")

    def set_hourly_rate(self, rate):
        if rate < 0:
            print("Giá phải không âm.")
            return
        self.hourly_rate = rate
        self.save_data()

    # ---------- Đặt chỗ và Check‑in/out ----------
    def reserve_slot(self, plate):
        plate = _require_non_blank(plate, "Plate")
        if plate is None:
            return None
        if any(s.reserved_for == plate or s.plate == plate for s in self.slots.values()):
            print(f"{plate} đã có slot được đặt trước hoặc đang đỗ.")
            return None
        free_slot = next((s for s in self.slots.values() if s.is_available and not s.reserved_for), None)
        if not free_slot:
            print("Không còn slot trống để đặt trước.")
            return None
        free_slot.reserved_for = plate
        self.save_data()
        print(f"Slot {free_slot.slot_id} đã được đặt trước cho {plate}.")
        return free_slot.slot_id

    def check_in_vehicle(self, plate):
        plate = _require_non_blank(plate, "Plate")
        if plate is None:
            return None
        if any(s.plate == plate for s in self.slots.values()):
            print(f"Xe {plate} đã có mặt trong bãi.")
            return None

        # Ưu tiên slot đã đặt trước
        slot = next((s for s in self.slots.values() if s.reserved_for == plate), None)
        if not slot:
            slot = next((s for s in self.slots.values() if s.is_available and not s.reserved_for), None)
        if not slot:
            print("Bãi đã đầy!")
            return None

        slot.is_available = False
        slot.plate = plate
        slot.check_in = datetime.now().isoformat()
        slot.reserved_for = None

        veh = self.vehicles.get(plate)
        if veh:
            veh.visit_count += 1
        else:
            self.vehicles[plate] = Vehicle(plate, visit_count=1)

        self._log_occupancy()
        self.save_data()
        print(f"Xe {plate} -> slot {slot.slot_id}")
        self._notify_if_almost_full()
        return slot.slot_id

    def check_out_vehicle(self, plate):
        slot = next((s for s in self.slots.values() if s.plate == plate), None)
        if not slot:
            print("Không tìm thấy xe trong bãi.")
            return None

        check_in_time = datetime.fromisoformat(slot.check_in)
        hours_exact = (datetime.now() - check_in_time).total_seconds() / 3600
        hours = max(1, math.floor(hours_exact + 0.5))
        fee = hours * self.hourly_rate

        self.transactions.append(Transaction(
            plate, slot.slot_id, slot.check_in, datetime.now().isoformat(), fee
        ))

        slot.is_available = True
        slot.plate = None
        slot.check_in = None

        self._log_occupancy()
        self.save_data()
        print(f"Xe {plate} đã rời khỏi bãi. {hours}h (làm tròn) - Phí: {fee:,}")
        return fee

    # ---------- Slot và thanh toán ----------
    def available_slots(self):
        """Trả về danh sách trạng thái của tất cả slot."""
        result = []
        for s in self.slots.values():
            status = "Còn chỗ" if (s.is_available and not s.reserved_for) else "Đã đầy"
            result.append(f"{s.slot_id} - {status}")
        return result

    def _unpaid_transactions(self, plate):
        return [t for t in self.transactions if t.plate == plate and not t.paid]

    def pending_fee(self, plate):
        unpaid = self._unpaid_transactions(plate)
        if not unpaid:
            print("Không có khoản phí chưa thanh toán cho biển số này.")
            return None
        total = sum(t.fee for t in unpaid)
        print(f"Phí chưa thanh toán cho {plate}: {total:,} ({len(unpaid)} phiên).")
        self._notify_if_overdue(unpaid)
        return total

    def pay_fee(self, plate):
        unpaid = self._unpaid_transactions(plate)
        if not unpaid:
            print("Không có khoản phí nào để thanh toán.")
            return None
        total = 0
        for t in unpaid:
            t.paid = True
            total += t.fee
        self.save_data()
        print(f"Đã thanh toán {total:,} cho {plate} ({len(unpaid)} phiên).")
        return total

    # ---------- Thông báo tự động (tính sáng tạo) ----------
    def _notify_if_almost_full(self):
        rate = self.occupancy_rate()
        if rate >= NOTIFY_OCCUPANCY_PCT:
            print(f"[THÔNG BÁO] Bãi đã đạt {rate}% sức chứa. Khuyến nghị hạn chế xe vào.")

    def _notify_if_overdue(self, unpaid_transactions):
        now = datetime.now()
        for t in unpaid_transactions:
            age_hours = (now - datetime.fromisoformat(t.check_out)).total_seconds() / 3600
            if age_hours >= OVERDUE_HOURS:
                print(f"[THÔNG BÁO] Khoản phí {t.fee:,} cho phiên tại slot {t.slot_id} "
                      f"đã quá hạn {age_hours:.1f} giờ.")

    # ---------- Báo cáo và thống kê ----------
    def revenue_report(self, period="all", mode="calendar"):
        """Tính doanh thu theo kỳ."""
        if period == "all":
            return sum(t.fee for t in self.transactions)

        now = datetime.now()
        if mode == "rolling":
            days = {"daily": 1, "weekly": 7, "monthly": 30}.get(period)
            return sum(
                t.fee for t in self.transactions
                if (now - datetime.fromisoformat(t.check_out)).days <= days
            )

        def in_period(check_out_dt):
            if period == "daily":
                return check_out_dt.date() == now.date()
            if period == "weekly":
                return check_out_dt.isocalendar()[:2] == now.isocalendar()[:2]
            if period == "monthly":
                return (check_out_dt.year, check_out_dt.month) == (now.year, now.month)
            return False

        return sum(
            t.fee for t in self.transactions
            if in_period(datetime.fromisoformat(t.check_out))
        )

    def export_revenue_report(self, period="all", mode="calendar", filename=None):
        """Xuất báo cáo doanh thu ra file CSV."""
        if filename is None:
            filename = REPORT_FILE.format(period=period)
        revenue = self.revenue_report(period, mode)
        with open(filename, "w", encoding="utf-8", newline="") as f:
            writer = csv.writer(f)
            writer.writerow(["Period", "Mode", "Total Revenue"])
            writer.writerow([period, mode, revenue])
        print(f"Báo cáo doanh thu đã được xuất ra {filename}")

    def occupancy_rate(self):
        if not self.slots:
            return 0
        occupied = sum(1 for s in self.slots.values() if not s.is_available)
        return round(occupied / len(self.slots) * 100, 2)

    def _log_occupancy(self):
        self.occupancy_log.append((datetime.now().isoformat(), self.occupancy_rate()))
        # Giới hạn log
        if len(self.occupancy_log) > MAX_OCCUPANCY_LOG:
            self.occupancy_log = self.occupancy_log[-MAX_OCCUPANCY_LOG:]

    def occupancy_history(self, last_n=10):
        return self.occupancy_log[-last_n:]

    def most_used_slots(self, top_n=3):
        counter = {}
        for t in self.transactions:
            counter[t.slot_id] = counter.get(t.slot_id, 0) + 1
        return sorted(counter.items(), key=lambda x: x[1], reverse=True)[:top_n]

    def export_to_csv(self, filename=CSV_FILE):
        with open(filename, "w", newline="", encoding="utf-8") as f:
            writer = csv.writer(f)
            writer.writerow(["-- Slots --"])
            writer.writerow(["slot_id", "is_available", "plate", "check_in", "reserved_for"])
            for s in self.slots.values():
                writer.writerow([s.slot_id, s.is_available, s.plate, s.check_in, s.reserved_for])
            writer.writerow([])
            writer.writerow(["-- Vehicles --"])
            writer.writerow(["plate", "first_seen", "visit_count"])
            for v in self.vehicles.values():
                writer.writerow([v.plate, v.first_seen, v.visit_count])
            writer.writerow([])
            writer.writerow(["-- Transactions --"])
            writer.writerow(["plate", "slot_id", "check_in", "check_out", "fee", "paid"])
            for t in self.transactions:
                writer.writerow([t.plate, t.slot_id, t.check_in, t.check_out, t.fee, t.paid])
        print(f"Dữ liệu đã được xuất ra {filename}")

    # ---------- Real‑time theo dõi slot cho Attendant ----------
    def live_slot_monitor(self):
        """Hiển thị trạng thái các slot và tự động làm mới mỗi 5 giây."""
        try:
            while True:
                os.system('cls' if os.name == 'nt' else 'clear')
                print("===== TRẠNG THÁI SLOT (Real‑time) =====")
                print(f"{'Slot ID':<10} {'Trạng thái':<12} {'Biển số':<12} {'Đặt trước'}")
                for sid, slot in self.slots.items():
                    if not slot.is_available:
                        status = "Đang đỗ"
                        plate = slot.plate or ""
                        reserved = ""
                    elif slot.reserved_for:
                        status = "Đặt trước"
                        plate = ""
                        reserved = slot.reserved_for
                    else:
                        status = "Trống"
                        plate = ""
                        reserved = ""
                    print(f"{sid:<10} {status:<12} {plate:<12} {reserved}")
                print("\n[Thoát: nhấn Ctrl+C]")
                time.sleep(5)
        except KeyboardInterrupt:
            print("\nĐã dừng theo dõi.")

    # ---------- Lưu / tải dữ liệu ----------
    def save_data(self):
        data = {
            "hourly_rate": self.hourly_rate,
            "users": self.users,
            "slots": [s.to_dict() for s in self.slots.values()],
            "vehicles": [v.to_dict() for v in self.vehicles.values()],
            "transactions": [t.to_dict() for t in self.transactions],
            "occupancy_log": self.occupancy_log,
        }
        with open(DATA_FILE, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)

    def load_data(self):
        if not os.path.exists(DATA_FILE):
            return
        with open(DATA_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        self.hourly_rate = data.get("hourly_rate", self.hourly_rate)
        self.users = data.get("users", self.users)
        # Tương thích ngược: dữ liệu cũ chưa có trường "status" -> coi là active
        for info in self.users.values():
            info.setdefault("status", STATUS_ACTIVE)
        self.slots = {s["slot_id"]: ParkingSlot.from_dict(s) for s in data.get("slots", [])}
        self.vehicles = {v["plate"]: Vehicle.from_dict(v) for v in data.get("vehicles", [])}
        self.transactions = [Transaction.from_dict(t) for t in data.get("transactions", [])]
        self.occupancy_log = [tuple(x) for x in data.get("occupancy_log", [])]

# -------------------- Hàm đăng nhập --------------------
def login_menu(lot, role_required):
    """Yêu cầu nhập username/password cho một role cụ thể."""
    attempts = 3
    while attempts > 0:
        username = input("Username: ").strip()
        password = input("Password: ").strip()
        role = lot.authenticate(username, password)
        if role == role_required:
            print(f"Đăng nhập thành công (vai trò: {role})")
            return True
        attempts -= 1
        print(f"Sai thông tin. Còn {attempts} lần thử.")
    print("Quá số lần thử. Quay lại menu chính.")
    return False

# -------------------- Đăng ký tài khoản --------------------
def register_menu(lot):
    print("\n===== ĐĂNG KÝ TÀI KHOẢN MỚI =====")
    print("1. Admin (cần Admin gốc duyệt trước khi đăng nhập được)")
    print("2. Attendant (cần Admin gốc duyệt trước khi đăng nhập được)")
    print("3. Vehicle Owner (được kích hoạt ngay, đăng nhập được luôn)")
    print("4. Quay lại")
    choice = input("Chọn vai trò muốn đăng ký: ").strip()

    role_map = {"1": "admin", "2": "attendant", "3": "owner"}
    if choice not in role_map:
        if choice != "4":
            print("Lựa chọn không hợp lệ.")
        return

    username = input("Tên đăng nhập mong muốn: ").strip()
    password = input("Mật khẩu: ").strip()
    confirm = input("Xác nhận mật khẩu: ").strip()
    if password != confirm:
        print("Mật khẩu xác nhận không khớp. Đăng ký thất bại.")
        return

    lot.register_user(username, password, role_map[choice])

# -------------------- Menu Admin gốc (Root Admin) --------------------
def root_menu(lot):
    while True:
        print("\n===== ROOT ADMIN MENU =====")
        print("1. Xem danh sách tài khoản đang chờ duyệt")
        print("2. Duyệt tài khoản (approve)")
        print("3. Từ chối tài khoản (reject)")
        print("4. Xem toàn bộ tài khoản trong hệ thống")
        print("5. Vào Admin Menu (quản lý bãi đỗ)")
        print("6. Đổi mật khẩu Root Admin")
        print("7. Thoát")
        choice = input("Chọn: ").strip()

        if choice == "1":
            pending = lot.pending_users()
            if not pending:
                print("Không có tài khoản nào đang chờ duyệt.")
            else:
                print("Tài khoản đang chờ duyệt:")
                for username, role in pending:
                    print(f" - {username} (vai trò: {role})")
        elif choice == "2":
            username = input("Tên đăng nhập cần duyệt: ").strip()
            lot.approve_user(username)
        elif choice == "3":
            username = input("Tên đăng nhập cần từ chối: ").strip()
            lot.reject_user(username)
        elif choice == "4":
            print("Toàn bộ tài khoản trong hệ thống:")
            for username, role, status in lot.list_users():
                print(f" - {username:<15} role={role:<10} status={status}")
        elif choice == "5":
            admin_menu(lot)
        elif choice == "6":
            old = input("Mật khẩu hiện tại: ").strip()
            new = input("Mật khẩu mới: ").strip()
            lot.change_password(DEFAULT_ROOT_USER, old, new)
        elif choice == "7":
            break
        else:
            print("Lựa chọn không hợp lệ.")

# -------------------- Menu cho từng vai trò --------------------
def admin_menu(lot):
    while True:
        print("\n===== ADMIN MENU =====")
        print("1. Cấu hình bãi (số slot, giá giờ)")
        print("2. Thêm slot")
        print("3. Cập nhật slot")
        print("4. Xóa slot")
        print("5. Doanh thu / Thống kê")
        print("6. Xuất dữ liệu CSV")
        print("7. Xuất báo cáo doanh thu ra file")
        print("8. Đổi mật khẩu admin")
        print("9. Thoát")
        choice = input("Chọn: ").strip()

        if choice == "1":
            try:
                n = int(input("Tổng số slot: "))
                r = float(input("Giá mỗi giờ: "))
            except ValueError:
                print("Dữ liệu không hợp lệ.")
                continue
            lot.configure_lot(n, r)
        elif choice == "2":
            lot.add_slot(input("ID slot mới: ").strip())
        elif choice == "3":
            sid = input("ID slot: ").strip()
            nid = input("ID mới (bỏ trống nếu giữ nguyên): ").strip() or None
            st = input("Có trống? (y/n/bỏ trống): ").strip().lower()
            avail = True if st == "y" else False if st == "n" else None
            lot.update_slot(sid, new_slot_id=nid, is_available=avail)
        elif choice == "4":
            lot.remove_slot(input("ID slot: ").strip())
        elif choice == "5":
            p = {"1": "daily", "2": "weekly", "3": "monthly", "4": "all"}.get(
                input("1.Daily 2.Weekly 3.Monthly 4.All: ").strip(), "all")
            m = {"1": "calendar", "2": "rolling"}.get(
                input("1.Calendar period 2.Rolling window: ").strip(), "calendar") if p != "all" else "calendar"
            rev = lot.revenue_report(p, mode=m)
            print(f"Doanh thu ({p}, {m}): {rev:,}")
            print("Tỉ lệ lấp đầy hiện tại:", lot.occupancy_rate(), "%")
            print("Lịch sử occupancy (10 gần nhất):", lot.occupancy_history())
            print("Các slot được sử dụng nhiều nhất:", lot.most_used_slots())
        elif choice == "6":
            lot.export_to_csv()
        elif choice == "7":
            p = {"1": "daily", "2": "weekly", "3": "monthly", "4": "all"}.get(
                input("1.Daily 2.Weekly 3.Monthly 4.All: ").strip(), "all")
            m = {"1": "calendar", "2": "rolling"}.get(
                input("1.Calendar period 2.Rolling window: ").strip(), "calendar") if p != "all" else "calendar"
            fname = input("Tên file (bỏ trống để dùng mặc định): ").strip() or None
            lot.export_revenue_report(p, m, fname)
        elif choice == "8":
            old = input("Mật khẩu hiện tại: ").strip()
            new = input("Mật khẩu mới: ").strip()
            lot.change_password(DEFAULT_ADMIN_USER, old, new)
        elif choice == "9":
            break
        else:
            print("Lựa chọn không hợp lệ.")

def attendant_menu(lot):
    while True:
        print("\n===== ATTENDANT MENU =====")
        print("1. Check‑in xe")
        print("2. Check‑out xe")
        print("3. Xem slot trống")
        print("4. Theo dõi trạng thái slot (Real‑time)")
        print("5. Đổi mật khẩu")
        print("6. Thoát")
        choice = input("Chọn: ").strip()

        if choice == "1":
            lot.check_in_vehicle(input("Biển số: ").strip())
        elif choice == "2":
            lot.check_out_vehicle(input("Biển số: ").strip())
        elif choice == "3":
            print("Slot trống:", lot.available_slots())
        elif choice == "4":
            lot.live_slot_monitor()
        elif choice == "5":
            old = input("Mật khẩu hiện tại: ").strip()
            new = input("Mật khẩu mới: ").strip()
            lot.change_password(DEFAULT_ATTENDANT_USER, old, new)
        elif choice == "6":
            break
        else:
            print("Lựa chọn không hợp lệ.")

def owner_menu(lot):
    while True:
        print("\n===== OWNER MENU =====")
        print("1. Xem slot trống")
        print("2. Xem giá giờ")
        print("3. Đặt trước slot")
        print("4. Xem phí chưa thanh toán")
        print("5. Thanh toán phí")
        print("6. Đổi mật khẩu")
        print("7. Thoát")
        choice = input("Chọn: ").strip()

        if choice == "1":
            print("Slot trống:", lot.available_slots())
        elif choice == "2":
            print(f"Giá mỗi giờ: {lot.hourly_rate:,}")
        elif choice == "3":
            lot.reserve_slot(input("Biển số: ").strip())
        elif choice == "4":
            lot.pending_fee(input("Biển số: ").strip())
        elif choice == "5":
            lot.pay_fee(input("Biển số: ").strip())
        elif choice == "6":
            old = input("Mật khẩu hiện tại: ").strip()
            new = input("Mật khẩu mới: ").strip()
            lot.change_password(DEFAULT_OWNER_USER, old, new)
        elif choice == "7":
            break
        else:
            print("Lựa chọn không hợp lệ.")

# -------------------- Hàm main --------------------
def main():
    lot = ParkingLot(hourly_rate=10000)
    while True:
        print("\n===== SMART PARKING MANAGEMENT SYSTEM =====")
        print("1. Đăng nhập - Admin")
        print("2. Đăng nhập - Attendant")
        print("3. Đăng nhập - Vehicle Owner")
        print("4. Đăng nhập - Root Admin (Admin gốc)")
        print("5. Đăng ký tài khoản mới")
        print("6. Thoát")
        role = input("Chọn: ").strip()

        if role == "1":
            if login_menu(lot, "admin"):
                admin_menu(lot)
        elif role == "2":
            if login_menu(lot, "attendant"):
                attendant_menu(lot)
        elif role == "3":
            if login_menu(lot, "owner"):
                owner_menu(lot)
        elif role == "4":
            if login_menu(lot, "root"):
                root_menu(lot)
        elif role == "5":
            register_menu(lot)
        elif role == "6":
            print("Tạm biệt!")
            break
        else:
            print("Lựa chọn không hợp lệ.")

# -------------------- Unit tests (giữ nguyên và cập nhật) --------------------
spms = sys.modules[__name__]

class SPMSTestCase(unittest.TestCase):
    def setUp(self):
        self._orig_data_file = spms.DATA_FILE
        spms.DATA_FILE = f"test_data_{id(self)}.json"
        if os.path.exists(spms.DATA_FILE):
            os.remove(spms.DATA_FILE)
        self.lot = ParkingLot(hourly_rate=10000)
        self.lot.configure_lot(total_slots=3, hourly_rate=10000)

    def tearDown(self):
        if os.path.exists(spms.DATA_FILE):
            os.remove(spms.DATA_FILE)
        spms.DATA_FILE = self._orig_data_file

    def test_check_in_assigns_free_slot(self):
        slot_id = self.lot.check_in_vehicle("51A-12345")
        self.assertIsNotNone(slot_id)
        self.assertFalse(self.lot.slots[slot_id].is_available)

    def test_check_in_duplicate_plate_rejected(self):
        self.lot.check_in_vehicle("51A-12345")
        result = self.lot.check_in_vehicle("51A-12345")
        self.assertIsNone(result)

    def test_lot_full_returns_none(self):
        self.lot.check_in_vehicle("A")
        self.lot.check_in_vehicle("B")
        self.lot.check_in_vehicle("C")
        result = self.lot.check_in_vehicle("D")
        self.assertIsNone(result)

    def test_check_out_computes_fee_min_one_hour(self):
        self.lot.check_in_vehicle("51A-12345")
        slot = next(s for s in self.lot.slots.values() if s.plate == "51A-12345")
        slot.check_in = datetime.now().isoformat()
        fee = self.lot.check_out_vehicle("51A-12345")
        self.assertEqual(fee, self.lot.hourly_rate)

    def test_round_half_up_hours(self):
        self.lot.check_in_vehicle("51A-99999")
        slot = next(s for s in self.lot.slots.values() if s.plate == "51A-99999")
        slot.check_in = (datetime.now() - timedelta(hours=2, minutes=30)).isoformat()
        fee = self.lot.check_out_vehicle("51A-99999")
        self.assertEqual(fee, 3 * self.lot.hourly_rate)

    def test_reservation_then_check_in_uses_reserved_slot(self):
        reserved = self.lot.reserve_slot("51A-11111")
        self.assertIsNotNone(reserved)
        assigned = self.lot.check_in_vehicle("51A-11111")
        self.assertEqual(reserved, assigned)

    def test_occupancy_rate(self):
        self.assertEqual(self.lot.occupancy_rate(), 0)
        self.lot.check_in_vehicle("A")
        self.assertAlmostEqual(self.lot.occupancy_rate(), 33.33, places=1)

    def test_most_used_slots(self):
        for plate in ["A", "B"]:
            self.lot.check_in_vehicle(plate)
            self.lot.check_out_vehicle(plate)
        top = self.lot.most_used_slots(top_n=1)
        self.assertEqual(len(top), 1)

    def test_revenue_report_all(self):
        self.lot.check_in_vehicle("A")
        self.lot.check_out_vehicle("A")
        self.assertEqual(self.lot.revenue_report("all"), self.lot.hourly_rate)

    def test_multiple_unpaid_fees_are_all_collected(self):
        plate = "51A-77777"
        self.lot.transactions.append(
            Transaction(plate, "P1", "2024-01-01T08:00:00", "2024-01-01T09:00:00", 10000, paid=False)
        )
        self.lot.transactions.append(
            Transaction(plate, "P2", "2024-01-02T08:00:00", "2024-01-02T10:00:00", 20000, paid=False)
        )
        total_pending = self.lot.pending_fee(plate)
        self.assertEqual(total_pending, 30000)
        paid_total = self.lot.pay_fee(plate)
        self.assertEqual(paid_total, 30000)
        self.assertTrue(all(t.paid for t in self.lot.transactions if t.plate == plate))

    def test_remove_slot_refuses_reserved_slot(self):
        reserved_id = self.lot.reserve_slot("51A-22222")
        before = len(self.lot.slots)
        self.lot.remove_slot(reserved_id)
        after = len(self.lot.slots)
        self.assertEqual(before, after)
        self.assertIn(reserved_id, self.lot.slots)

    def test_remove_slot_refuses_occupied_slot(self):
        slot_id = self.lot.check_in_vehicle("51A-33333")
        self.lot.remove_slot(slot_id)
        self.assertIn(slot_id, self.lot.slots)

    def test_blank_plate_and_slot_rejected(self):
        self.assertIsNone(self.lot.check_in_vehicle("   "))
        self.assertIsNone(self.lot.reserve_slot(""))
        self.lot.add_slot("   ")
        self.assertNotIn("   ", self.lot.slots)

    def test_admin_login_password(self):
        # Mật khẩu mặc định đã được băm
        self.assertIsNone(self.lot.authenticate("admin", "wrong"))
        self.assertEqual(self.lot.authenticate("admin", "admin123"), "admin")
        ok = self.lot.change_password("admin", "admin123", "newpass")
        self.assertTrue(ok)
        self.assertEqual(self.lot.authenticate("admin", "newpass"), "admin")

    def test_register_owner_active_immediately(self):
        ok = self.lot.register_user("owner_new", "pass123", "owner")
        self.assertTrue(ok)
        self.assertEqual(self.lot.authenticate("owner_new", "pass123"), "owner")

    def test_register_admin_requires_root_approval(self):
        ok = self.lot.register_user("admin_new", "pass123", "admin")
        self.assertTrue(ok)
        # Chưa được duyệt -> không đăng nhập được dù đúng mật khẩu
        self.assertIsNone(self.lot.authenticate("admin_new", "pass123"))
        self.assertIn(("admin_new", "admin"), self.lot.pending_users())
        # Root duyệt -> đăng nhập được
        approved = self.lot.approve_user("admin_new")
        self.assertTrue(approved)
        self.assertEqual(self.lot.authenticate("admin_new", "pass123"), "admin")

    def test_register_attendant_rejected_cannot_login(self):
        self.lot.register_user("att_new", "pass123", "attendant")
        rejected = self.lot.reject_user("att_new")
        self.assertTrue(rejected)
        self.assertIsNone(self.lot.authenticate("att_new", "pass123"))

    def test_register_duplicate_username_rejected(self):
        self.lot.register_user("dup_user", "pass123", "owner")
        ok = self.lot.register_user("dup_user", "otherpass", "owner")
        self.assertFalse(ok)

    def test_root_admin_default_login(self):
        self.assertEqual(self.lot.authenticate(DEFAULT_ROOT_USER, DEFAULT_ROOT_PASSWORD), "root")

    def test_persistence_round_trip(self):
        self.lot.check_in_vehicle("51A-44444")
        self.lot.save_data()
        reloaded = ParkingLot(hourly_rate=999)
        self.assertEqual(reloaded.hourly_rate, self.lot.hourly_rate)
        self.assertIn("51A-44444", [s.plate for s in reloaded.slots.values()])

def run_tests():
    unittest.main(argv=[sys.argv[0]] + sys.argv[2:], module=__name__, exit=True)

if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "test":
        run_tests()
    else:
        main()