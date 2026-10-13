FROM python:3.12-slim-bookworm

# - PYTHONUNBUFFERED: stream logs to Render in real time
# - PIP_NO_CACHE_DIR: keep the image small
ENV PYTHONUNBUFFERED=1 \
    PYTHONDONTWRITEBYTECODE=1 \
    PIP_NO_CACHE_DIR=1 \
    DEBIAN_FRONTEND=noninteractive

# ffmpeg is required by PyTgCalls for voice/video streams.
# git + build-essential cover any dependency that has no prebuilt wheel.
RUN apt-get update && apt-get install -y --no-install-recommends \
        ffmpeg \
        git \
        build-essential \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /app

# Install Python deps first so this layer is cached between code changes
COPY requirements.txt .
RUN pip install --upgrade pip && pip install -r requirements.txt

# Copy the application
COPY . .

# Render injects $PORT at runtime; the app reads it (see main.py).
# No EXPOSE needed on Render, but it documents the local default.
EXPOSE 20826

CMD ["python", "main.py"]
