#!/usr/bin/env python3
"""
Example File Generator for Unified Typing Video Studio
======================================================
Run this script once to generate example files in the 'input/' directory.

Junior vs Senior examples are saved as JSON files containing both
the junior and senior code in a single structured file.
"""
import os
import json
from pathlib import Path

INPUT_DIR = Path.cwd() / "input"
INPUT_DIR.mkdir(parents=True, exist_ok=True)

EXAMPLES = {
    # ==========================================
    # 1. MULTI-WINDOW MODE EXAMPLES
    # ==========================================
    "mw_1_bubble.py": """def bubble_sort(arr):
    n = len(arr)
    for i in range(n):
        for j in range(0, n-i-1):
            if arr[j] > arr[j+1]:
                arr[j], arr[j+1] = arr[j+1], arr[j]
    return arr
""",
    "mw_1_quick.py": """def quick_sort(arr):
    if len(arr) <= 1:
        return arr
    pivot = arr[len(arr) // 2]
    left = [x for x in arr if x < pivot]
    middle = [x for x in arr if x == pivot]
    right = [x for x in arr if x > pivot]
    return quick_sort(left) + middle + quick_sort(right)
""",
    "mw_2_old_api.js": """function fetchUser(id) {
    return fetch('/api/users/' + id)
        .then(res => res.json())
        .catch(err => console.error(err));
}
""",
    "mw_2_new_api.js": """const fetchUser = async (id) => {
    try {
        const res = await fetch(`/api/users/${id}`);
        return await res.json();
    } catch (err) {
        console.error(err);
    }
};
""",
    "mw_3_list.py": """class Node:
    def __init__(self, data):
        self.data = data
        self.next = None
""",
    "mw_3_doubly.py": """class Node:
    def __init__(self, data):
        self.data = data
        self.next = None
        self.prev = None
""",
    "mw_4_sync_a.py": """import time
print("Starting sync process...")
time.sleep(1)
print("Sync complete!")
""",
    "mw_4_sync_b.py": """import threading
def sync():
    print("Thread started...")
    threading.Event().wait(1)
    print("Thread finished!")
""",
    "mw_5_buggy.py": """def divide(a, b):
    return a / b  # Bug: no zero division check!
""",
    "mw_5_fixed.py": """def divide(a, b):
    if b == 0:
        raise ValueError("Cannot divide by zero!")
    return a / b
""",

    # ==========================================
    # 2. JUNIOR VS SENIOR MODE EXAMPLES (JSON)
    # ==========================================
    "jr_1_stats.json": {
        "title": "Statistics Function",
        "language": "python",
        "description": "Junior uses basic logic with no error handling; Senior uses standard library and type hints.",
        "junior_code": """def get_stats(nums):
    avg = sum(nums) / len(nums)
    m = max(nums)
    # hardcoded logic, no error handling
    return avg, m
""",
        "senior_code": """from statistics import mean
from typing import List, Tuple

def get_stats(nums: List[float]) -> Tuple[float, float]:
    if not nums:
        raise ValueError("List cannot be empty")
    return mean(nums), max(nums)
"""
    },
    "jr_2_url.json": {
        "title": "URL Builder",
        "language": "python",
        "description": "Junior manually concatenates strings; Senior uses urllib.parse.urlencode.",
        "junior_code": """def build_url(base, params):
    url = base + "?"
    for k, v in params.items():
        url += k + "=" + str(v) + "&"
    return url[:-1]
""",
        "senior_code": """from urllib.parse import urlencode

def build_url(base: str, params: dict) -> str:
    return f"{base}?{urlencode(params)}"
"""
    },
    "jr_3_requests.json": {
        "title": "HTTP Request Handler",
        "language": "python",
        "description": "Junior crashes on non-200 responses; Senior handles timeouts and exceptions properly.",
        "junior_code": """import requests
def get_data(url):
    r = requests.get(url)
    return r.json() # crashes if not 200 OK
""",
        "senior_code": """import requests
from requests.exceptions import RequestException

def get_data(url: str, timeout: int = 5) -> dict:
    try:
        r = requests.get(url, timeout=timeout)
        r.raise_for_status()
        return r.json()
    except RequestException as e:
        print(f"Error: {e}")
        return {}
"""
    },
    "jr_4_dataclass.json": {
        "title": "User Model",
        "language": "python",
        "description": "Junior uses a plain class with a long parameter list; Senior uses @dataclass for clarity.",
        "junior_code": """class User:
    def __init__(self, name, age, email, role):
        self.name = name
        self.age = age
        self.email = email
        self.role = role # long parameter list
""",
        "senior_code": """from dataclasses import dataclass

@dataclass
class User:
    name: str
    age: int
    email: str
    role: str = "viewer"
"""
    },
    "jr_5_comprehension.json": {
        "title": "Data Processing",
        "language": "python",
        "description": "Junior uses a verbose for-loop; Senior uses a list comprehension with type hints.",
        "junior_code": """def process_data(data):
    result = []
    for item in data:
        if item > 10:
            result.append(item * 2)
    return result
""",
        "senior_code": """def process_data(data: list) -> list:
    return [item * 2 for item in data if item > 10]
"""
    },

    # ==========================================
    # 3. CODE YT MODE EXAMPLES
    # ==========================================
    "yt_1_python.py": """# Python Decorators Explained
import time
from functools import wraps

def timer(func):
    @wraps(func)
    def wrapper(*args, **kwargs):
        start = time.perf_counter()
        result = func(*args, **kwargs)
        end = time.perf_counter()
        print(f"{func.__name__} took {end-start:.4f} secs")
        return result
    return wrapper

@timer
def long_running_task():
    time.sleep(1)
    return "Done!"

long_running_task()
""",
    "yt_2_javascript.js": """// ES6 Array Methods Demystified
const users = [
    { name: 'Alice', age: 25, active: true },
    { name: 'Bob', age: 30, active: false },
    { name: 'Charlie', age: 35, active: true }
];

const activeUserNames = users
    .filter(user => user.active)
    .map(user => user.name)
    .sort();

console.log(activeUserNames); // ['Alice', 'Charlie']
""",
    "yt_3_async.py": """import asyncio

async def fetch_data(id: int) -> str:
    print(f"Fetching data {id}...")
    await asyncio.sleep(2)
    return f"Data_{id}"

async def main():
    tasks = [fetch_data(i) for i in range(3)]
    results = await asyncio.gather(*tasks)
    print(results)

asyncio.run(main())
""",
    "yt_4_regex.py": r"""import re

# Extracting emails from text
text = "Contact us at support@example.com or sales@test.org"
pattern = r'\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Z|a-z]{2,7}\b'

emails = re.findall(pattern, text)
print(emails)
""",
    "yt_5_classes.py": """from abc import ABC, abstractmethod

class Shape(ABC):
    @abstractmethod
    def area(self) -> float:
        pass

class Circle(Shape):
    def __init__(self, radius: float):
        self.radius = radius

    def area(self) -> float:
        return 3.14159 * (self.radius ** 2)

c = Circle(5)
print(f"Area: {c.area():.2f}")
""",

    # ==========================================
    # 4. TEXT & EMOJI MODE EXAMPLES
    # ==========================================
    "txt_1_chat.txt": """Developer: Hey, did you push the latest commit? 🚀
Reviewer: Not yet, I'm reviewing the PR. 🔍
Developer: Take your time, but the client is asking. ⏳
Reviewer: Ok, done! Merged it. ✅ 
Developer: Awesome! Party time! 🎉
""",
    "txt_2_emoji.emoji": """Welcome to the Emoji Typing Test! ✨
Here are some shortcodes: :rocket: :fire: :heart: :check: 
Let's see how fast you can type them! ⌨️💨
""",
    "txt_3_ascii.ascii": r"""
      _.--.--.--.
    .'|  |  |  |`\
   /  |  |  |  |  \
  |   |  |  |  |   |
  |   |  |  |  |   |
   \  |  |  |  |  /
    `'.|__|__|__.'`
     ASCII ART MODE
   [ Centered Text ]
""",
    "txt_4_markdown.md": '''# Markdown Support Demo

You can use **bold** text and *italic* text.

## Inline Code
Use single backticks for code like `print("hello")`.

## Lists
1. First item
2. Second item
3. Third item

> Blockquotes are also supported!
''',
    "txt_5_story.txt": """Once upon a time, there was a programmer who typed code all day. ⌨️
They dreamed of creating the ultimate typing video. 🎬
With patience and practice, their dream came true. 🌟
The End.
"""
}

# ==========================================
# FILE GENERATION LOGIC
# ==========================================
if __name__ == "__main__":
    print(f"Generating {len(EXAMPLES)} example files in: {INPUT_DIR}\n")
    
    for filename, content in EXAMPLES.items():
        filepath = INPUT_DIR / filename
        
        if isinstance(content, dict):
            # Junior vs Senior JSON file
            with open(filepath, "w", encoding="utf-8") as f:
                json.dump(content, f, indent=4, ensure_ascii=False)
            print(f"  ✅ Created {filename}  (JSON: {content.get('title', '?')})")
        else:
            # Regular text/code file
            with open(filepath, "w", encoding="utf-8") as f:
                f.write(content)
            print(f"  ✅ Created {filename}")
        
    print(f"\nDone! All examples are ready in the 'input/' folder.")
    print(f"   - Multi-Window:  10 files (.py/.js)")
    print(f"   - Jr vs Senior:    5 files (.json)")
    print(f"   - Code YT:         5 files (.py/.js)")
    print(f"   - Text & Emoji:    5 files (.txt/.emoji/.ascii/.md)")
    print(f"   Total: {len(EXAMPLES)} files")