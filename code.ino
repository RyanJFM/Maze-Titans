#include <Wire.h>
#include <Adafruit_VL53L0X.h>
#include <Adafruit_MPU6050.h>
#include <Adafruit_Sensor.h>

// ===================== TCA + VL53L0X =====================
#define TCA_ADDR   0x70

#define CH_FRONT   0
#define CH_LEFT    1
#define CH_FLEFT   2   // angled ~35° to left
#define CH_FRIGHT  3   // angled ~35° to right
#define CH_RIGHT   4   // your right sensor channel

Adafruit_VL53L0X vlx;
bool tofOK_front=false, tofOK_left=false, tofOK_right=false, tofOK_fleft=false, tofOK_fright=false;

// ===================== MPU6050 =====================
Adafruit_MPU6050 mpu;
bool mpuOK=false;

float gyroZ_bias = 0.0f;  // rad/s bias
float yaw_deg = 0.0f;
unsigned long lastYawMs = 0;

// ===================== TB6612FNG Pins =====================
const int AIN1 = 26;
const int AIN2 = 27;
const int PWMA = 14;

const int BIN1 = 16;
const int BIN2 = 33;
const int PWMB = 13;

const int STBY = 25;

// ===================== Encoder Pins =====================
const int LEFT_ENC_A  = 34;
const int RIGHT_ENC_A = 36;

volatile long leftTicks = 0;
volatile long rightTicks = 0;

// ===================== PWM (ESP32 core v3.x) =====================
const int PWM_FREQ = 20000;
const int PWM_RES  = 8;     // duty 0..255

// ===================== Tuned Parameters =====================
int   BASE_PWM       = 35;
int   PWM_MAX        = 120;
int   TICKS_PER_CELL = 328;

int   OFFSET_MM      = 15;
int   WALL_MM        = 85;

// sensor fusion
float K_DIST         = 0.45f; // PWM/mm
int   DIST_DB_MM     = 1;

float K_ENC          = 0.40f; // PWM/tick

float K_YAW          = 0.55f; // PWM/deg
float YAW_DB_DEG     = 1.0f;
int   YAW_SIGN       = -1;

float W_DIST_BOTH    = 1.00f;
float W_YAW_BOTH     = 0.35f;

float W_DIST_OPEN    = 0.25f;
float W_YAW_OPEN     = 1.00f;

// turn tuning
int   TURN_PWM       = 55;
int   TURN_TICKS_90  = 115;
float TURN_TOL_DEG   = 2.0f;

// optional safety (prevents crashing if a wall appears mid-cell)
int   FRONT_STOP_MM  = 60;   // if front < this while moving, stop & abort the step
int   FRONT_DB_MM    = 5;

// ===================== Maze / Floodfill (16x16) =====================
static const int N = 16;
// bit0=N, bit1=E, bit2=S, bit3=W
uint8_t  wallMask[N][N];
uint8_t  seenMask[N][N];
uint16_t costArr[N][N];

int xCell = 0;
int yCell = 0;
int heading = 0; // 0=N,1=E,2=S,3=W
long cellsTraveled = 0;

bool runningSearch = false;

// ===================== Telemetry =====================
int  lastFrontMM=-1, lastLeftMM=-1, lastRightMM=-1, lastFLeftMM=-1, lastFRightMM=-1;
bool wallFront=false, wallLeft=false, wallRight=false;
int  lastErrMM=0;
long lastEncErr=0;
int  lastPwmL=0, lastPwmR=0;

// ===================== Median-of-3 filter =====================
struct Med3 { int v[3]; uint8_t idx; };
Med3 fbuf{{-1,-1,-1},0}, lbuf{{-1,-1,-1},0}, rbuf{{-1,-1,-1},0}, flbuf{{-1,-1,-1},0}, frbuf{{-1,-1,-1},0};

static inline int median3(int a,int b,int c){
  if (a > b) { int t=a; a=b; b=t; }
  if (b > c) { int t=b; b=c; c=t; }
  if (a > b) { int t=a; a=b; b=t; }
  return b;
}
static inline void medPush(Med3 &b, int val){ b.v[b.idx]=val; b.idx=(b.idx+1)%3; }
static inline int  medValue(const Med3 &b){ return median3(b.v[0], b.v[1], b.v[2]); }

// ===================== Queue for BFS =====================
uint8_t qx[512], qy[512];
int qh=0, qt=0;
static inline void qReset(){ qh=qt=0; }
static inline bool qEmpty(){ return qh==qt; }
static inline void qPush(uint8_t x,uint8_t y){
  qx[qt]=x; qy[qt]=y; qt++; if(qt>=512) qt=0;
}
static inline void qPop(uint8_t &x,uint8_t &y){
  x=qx[qh]; y=qy[qh]; qh++; if(qh>=512) qh=0;
}

// ===================== Interrupts =====================
void IRAM_ATTR leftEncoderISR(){ leftTicks++; }
void IRAM_ATTR rightEncoderISR(){ rightTicks++; }

// ===================== Small helpers =====================
static inline void resetEncoders(){
  noInterrupts(); leftTicks=0; rightTicks=0; interrupts();
}
static inline long avgTicks(){ return (leftTicks + rightTicks)/2; }

static inline int dxForDir(int d){ if(d==1) return 1; if(d==3) return -1; return 0; }
static inline int dyForDir(int d){ if(d==0) return 1; if(d==2) return -1; return 0; }
static inline bool inBounds(int nx,int ny){ return nx>=0 && nx<N && ny>=0 && ny<N; }
static inline int relToAbs(int rel){ return (heading + rel) & 3; } // rel: 0F 1R 2B 3L
static inline int oppositeDir(int d){ return (d+2)&3; }

static inline bool isGoal(int x,int y){
  return ( (x==7 || x==8) && (y==7 || y==8) );
}

// ===================== Motor control =====================
void stopMotors(){
  ledcWrite(PWMA, 0);
  ledcWrite(PWMB, 0);
  lastPwmL = 0;
  lastPwmR = 0;
}

void setSignedPWM(int pwmL, int pwmR){
  int cmdL = constrain(pwmL, -PWM_MAX, PWM_MAX);
  int cmdR = constrain(pwmR, -PWM_MAX, PWM_MAX);

  if (cmdL >= 0){ digitalWrite(AIN1, HIGH); digitalWrite(AIN2, LOW); }
  else          { digitalWrite(AIN1, LOW);  digitalWrite(AIN2, HIGH); }

  if (cmdR >= 0){ digitalWrite(BIN1, HIGH); digitalWrite(BIN2, LOW); }
  else          { digitalWrite(BIN1, LOW);  digitalWrite(BIN2, HIGH); }

  ledcWrite(PWMA, abs(cmdL));
  ledcWrite(PWMB, abs(cmdR));

  lastPwmL = cmdL;
  lastPwmR = cmdR;
}

// ===================== TCA / ToF =====================
void tcaSelect(uint8_t ch){
  Wire.beginTransmission(TCA_ADDR);
  Wire.write(1 << ch);
  Wire.endTransmission();
}

int readToFOnce(uint8_t ch, bool ok){
  if(!ok) return -1;
  VL53L0X_RangingMeasurementData_t m;
  tcaSelect(ch);
  vlx.rangingTest(&m, false);
  if(m.RangeStatus == 4) return -1;
  int mm = (int)m.RangeMilliMeter - OFFSET_MM;
  if(mm < 0) mm = 0;
  return mm;
}

int readFrontMM()  { int v=readToFOnce(CH_FRONT ,tofOK_front ); medPush(fbuf ,v); return medValue(fbuf ); }
int readLeftMM()   { int v=readToFOnce(CH_LEFT  ,tofOK_left  ); medPush(lbuf ,v); return medValue(lbuf ); }
int readRightMM()  { int v=readToFOnce(CH_RIGHT ,tofOK_right ); medPush(rbuf ,v); return medValue(rbuf ); }
int readFLeftMM()  { int v=readToFOnce(CH_FLEFT ,tofOK_fleft ); medPush(flbuf,v); return medValue(flbuf); }
int readFRightMM() { int v=readToFOnce(CH_FRIGHT,tofOK_fright); medPush(frbuf,v); return medValue(frbuf); }

// ===================== Yaw =====================
void resetYaw(){
  yaw_deg = 0.0f;
  lastYawMs = millis();
}

void calibrateGyroZ(int samples=600, int delayMs=5){
  if(!mpuOK) return;
  float sum = 0;
  sensors_event_t a,g,t;
  for(int i=0;i<samples;i++){
    mpu.getEvent(&a,&g,&t);
    sum += g.gyro.z;
    delay(delayMs);
  }
  gyroZ_bias = sum / samples;
}

void updateYaw(){
  if(!mpuOK) return;

  unsigned long now = millis();
  float dt = (now - lastYawMs) * 0.001f;
  if(dt <= 0) dt = 0.001f;
  lastYawMs = now;

  sensors_event_t a,g,t;
  mpu.getEvent(&a,&g,&t);

  float gz = (g.gyro.z - gyroZ_bias) * (float)YAW_SIGN; // rad/s
  float gz_deg = gz * 57.2957795f; // deg/s
  yaw_deg += gz_deg * dt;
}

// ===================== Maze map update =====================
void setWallKnown(int cx,int cy,int absDir,bool isWall){
  seenMask[cx][cy] |= (1<<absDir);
  if(isWall) wallMask[cx][cy] |= (1<<absDir);
  else       wallMask[cx][cy] &= ~(1<<absDir);

  int nx = cx + dxForDir(absDir);
  int ny = cy + dyForDir(absDir);
  if(inBounds(nx,ny)){
    int od = oppositeDir(absDir);
    seenMask[nx][ny] |= (1<<od);
    if(isWall) wallMask[nx][ny] |= (1<<od);
    else       wallMask[nx][ny] &= ~(1<<od);
  }
}

bool isBlockedKnownWall(int cx,int cy,int absDir){
  if(seenMask[cx][cy] & (1<<absDir)){
    return (wallMask[cx][cy] & (1<<absDir));
  }
  return false; // unknown treated open
}

void exploreCell(){
  int f  = readFrontMM();
  int l  = readLeftMM();
  int r  = readRightMM();
  int fl = readFLeftMM();
  int fr = readFRightMM();

  lastFrontMM=f; lastLeftMM=l; lastRightMM=r; lastFLeftMM=fl; lastFRightMM=fr;

  // main walls from straight sensors (more reliable for grid walls)
  wallFront = (f > 0 && f < WALL_MM);
  wallLeft  = (l > 0 && l < WALL_MM);
  wallRight = (r > 0 && r < WALL_MM);

  // if front is invalid, fall back to angled pair
  if(f < 0){
    bool flHit = (fl > 0 && fl < WALL_MM);
    bool frHit = (fr > 0 && fr < WALL_MM);
    wallFront = (flHit && frHit);
  }

  setWallKnown(xCell, yCell, relToAbs(0), wallFront);
  setWallKnown(xCell, yCell, relToAbs(3), wallLeft);
  setWallKnown(xCell, yCell, relToAbs(1), wallRight);

  // boundaries
  if(xCell==0)     setWallKnown(xCell,yCell,3,true);
  if(xCell==N-1)   setWallKnown(xCell,yCell,1,true);
  if(yCell==0)     setWallKnown(xCell,yCell,2,true);
  if(yCell==N-1)   setWallKnown(xCell,yCell,0,true);
}

// ===================== Floodfill recompute (BFS) =====================
void recomputeCosts(){
  for(int i=0;i<N;i++) for(int j=0;j<N;j++) costArr[i][j]=65535;

  qReset();
  for(int gx=7; gx<=8; gx++){
    for(int gy=7; gy<=8; gy++){
      costArr[gx][gy]=0;
      qPush(gx,gy);
    }
  }

  while(!qEmpty()){
    uint8_t cx, cy;
    qPop(cx, cy);
    uint16_t c = costArr[cx][cy];

    for(int d=0; d<4; d++){
      if(isBlockedKnownWall(cx,cy,d)) continue;
      int nx = (int)cx + dxForDir(d);
      int ny = (int)cy + dyForDir(d);
      if(!inBounds(nx,ny)) continue;

      if(costArr[nx][ny] > c + 1){
        costArr[nx][ny] = c + 1;
        qPush((uint8_t)nx,(uint8_t)ny);
      }
    }
  }
}

// ===================== Choose next move =====================
int bestRelMove(){
  int relOrder[4] = {0,3,1,2}; // F, L, R, B
  uint16_t bestC = 65535;
  int bestRel = 2;

  for(int k=0;k<4;k++){
    int rel = relOrder[k];
    int absD = relToAbs(rel);
    if(isBlockedKnownWall(xCell,yCell,absD)) continue;

    int nx = xCell + dxForDir(absD);
    int ny = yCell + dyForDir(absD);
    if(!inBounds(nx,ny)) continue;

    if(costArr[nx][ny] < bestC){
      bestC = costArr[nx][ny];
      bestRel = rel;
    }
  }
  return bestRel;
}

// ===================== Forward (1 cell) fusion =====================
// Returns true if completed the cell, false if stopped early (unexpected wall)
bool driveOneCell(){
  resetEncoders();
  resetYaw();

  while(avgTicks() < TICKS_PER_CELL){
    updateYaw();

    // safety: stop if very close to a wall in front
    int f = readFrontMM();
    if(f > 0 && f < FRONT_STOP_MM){
      stopMotors();
      delay(120);
      Serial.println("FRONT STOP (wall too close) - aborting this step");
      return false;
    }

    int l = readLeftMM();
    int r = readRightMM();
    lastLeftMM=l; lastRightMM=r;

    bool leftWall  = (l > 0 && l < WALL_MM);
    bool rightWall = (r > 0 && r < WALL_MM);

    float wDist = (leftWall && rightWall) ? W_DIST_BOTH : W_DIST_OPEN;
    float wYaw  = (leftWall && rightWall) ? W_YAW_BOTH  : W_YAW_OPEN;

    int errMM = 0;
    if(leftWall && rightWall){
      errMM = l - r;
      if(abs(errMM) <= DIST_DB_MM) errMM = 0;
    }
    lastErrMM = errMM;

    float distCorr = wDist * K_DIST * (float)errMM;

    long encErr = leftTicks - rightTicks;
    lastEncErr = encErr;
    float encCorr = K_ENC * (float)encErr;

    float yawErr = yaw_deg;
    if(fabs(yawErr) <= YAW_DB_DEG) yawErr = 0;
    float yawCorr = wYaw * K_YAW * yawErr;

    float pwmLf = (float)BASE_PWM - distCorr - encCorr + yawCorr;
    float pwmRf = (float)BASE_PWM + distCorr + encCorr - yawCorr;

    setSignedPWM((int)lround(pwmLf), (int)lround(pwmRf));
    delay(20);
  }

  stopMotors();
  delay(120);

  xCell += dxForDir(heading);
  yCell += dyForDir(heading);
  cellsTraveled++;
  return true;
}

// ===================== Turns (90 / 180 via 2×90) =====================
void turn90Left(){
  resetEncoders();
  resetYaw();

  while(true){
    updateYaw();
    bool ticksOK = (avgTicks() >= TURN_TICKS_90);
    bool yawOK   = (fabs(yaw_deg) >= (90.0f - TURN_TOL_DEG));

    setSignedPWM(-TURN_PWM, +TURN_PWM);
    delay(10);

    if(ticksOK || yawOK) break;
  }
  stopMotors();
  delay(120);
  heading = (heading + 3) & 3;
}

void turn90Right(){
  resetEncoders();
  resetYaw();

  while(true){
    updateYaw();
    bool ticksOK = (avgTicks() >= TURN_TICKS_90);
    bool yawOK   = (fabs(yaw_deg) >= (90.0f - TURN_TOL_DEG));

    setSignedPWM(+TURN_PWM, -TURN_PWM);
    delay(10);

    if(ticksOK || yawOK) break;
  }
  stopMotors();
  delay(120);
  heading = (heading + 1) & 3;
}

void turn180(){
  turn90Right();
  turn90Right();
}

bool executeRelMove(int rel){
  if(rel==0){
    return driveOneCell();
  } else if(rel==3){
    turn90Left();
    return driveOneCell();
  } else if(rel==1){
    turn90Right();
    return driveOneCell();
  } else {
    turn180();
    return driveOneCell();
  }
}

// ===================== Reset maze =====================
void resetMaze(){
  for(int i=0;i<N;i++){
    for(int j=0;j<N;j++){
      wallMask[i][j]=0;
      seenMask[i][j]=0;
      costArr[i][j]=65535;
    }
  }
  xCell=0; yCell=0; heading=0; cellsTraveled=0;

  fbuf = Med3{{-1,-1,-1},0};
  lbuf = Med3{{-1,-1,-1},0};
  rbuf = Med3{{-1,-1,-1},0};
  flbuf = Med3{{-1,-1,-1},0};
  frbuf = Med3{{-1,-1,-1},0};

  lastFrontMM=lastLeftMM=lastRightMM=lastFLeftMM=lastFRightMM=-1;
  wallFront=wallLeft=wallRight=false;
  lastErrMM=0; lastEncErr=0; lastPwmL=0; lastPwmR=0;

  recomputeCosts();
}

// ===================== Setup =====================
void setup(){
  Serial.begin(115200);
  delay(200);

  pinMode(AIN1, OUTPUT); pinMode(AIN2, OUTPUT);
  pinMode(BIN1, OUTPUT); pinMode(BIN2, OUTPUT);
  pinMode(STBY, OUTPUT);
  digitalWrite(STBY, HIGH);

  // ESP32 core v3.x style
  ledcAttach(PWMA, PWM_FREQ, PWM_RES);
  ledcAttach(PWMB, PWM_FREQ, PWM_RES);
  stopMotors();

  pinMode(LEFT_ENC_A, INPUT);
  pinMode(RIGHT_ENC_A, INPUT);
  attachInterrupt(digitalPinToInterrupt(LEFT_ENC_A), leftEncoderISR, RISING);
  attachInterrupt(digitalPinToInterrupt(RIGHT_ENC_A), rightEncoderISR, RISING);

  Wire.begin(21,22);

  Serial.println("Init VL53L0X (5 sensors on TCA) ...");

  tcaSelect(CH_FRONT);  tofOK_front  = vlx.begin();
  Serial.println(tofOK_front  ? "Front  OK (CH0)" : "Front  FAIL (CH0)");

  tcaSelect(CH_LEFT);   tofOK_left   = vlx.begin();
  Serial.println(tofOK_left   ? "Left   OK (CH1)" : "Left   FAIL (CH1)");

  tcaSelect(CH_FLEFT);  tofOK_fleft  = vlx.begin();
  Serial.println(tofOK_fleft  ? "FLeft  OK (CH2)" : "FLeft  FAIL (CH2)");

  tcaSelect(CH_FRIGHT); tofOK_fright = vlx.begin();
  Serial.println(tofOK_fright ? "FRight OK (CH3)" : "FRight FAIL (CH3)");

  tcaSelect(CH_RIGHT);  tofOK_right  = vlx.begin();
  Serial.println(tofOK_right  ? "Right  OK (CH4)" : "Right  FAIL (CH4)");

  Serial.println("Init MPU6050...");
  mpuOK = mpu.begin();
  Serial.println(mpuOK ? "MPU OK" : "MPU FAIL");
  if(mpuOK){
    mpu.setAccelerometerRange(MPU6050_RANGE_8_G);
    mpu.setGyroRange(MPU6050_RANGE_500_DEG);
    mpu.setFilterBandwidth(MPU6050_BAND_21_HZ);
    delay(200);
    Serial.println("Calibrating gyro... keep robot STILL");
    calibrateGyroZ();
    Serial.print("GyroZ bias (rad/s): "); Serial.println(gyroZ_bias, 6);
  }

  resetMaze();

  Serial.println("AUTO-START in 5 seconds...");
  delay(5000);

  resetEncoders();
  resetYaw();
  runningSearch = true;
  Serial.println("STARTED SEARCH RUN ");
}

// ===================== Loop =====================
void loop(){
  if(!runningSearch) return;

  if(isGoal(xCell,yCell)){
    runningSearch = false;
    stopMotors();
    Serial.println("GOAL REACHED ");
    Serial.print("Cells traveled: "); Serial.println(cellsTraveled);
    return;
  }

  // Sense at cell center
  exploreCell();

  // Recompute floodfill
  recomputeCosts();

  // Choose
  int rel = bestRelMove();

  // Execute (if stopped early, just re-sense + replan without updating cell)
  bool ok = executeRelMove(rel);
  if(!ok){
    // stopped by FRONT_STOP_MM; do not move cell
    // next loop will explore same cell and choose a different move
    delay(50);
  }

  // Debug print
  Serial.print("Cell=("); Serial.print(xCell); Serial.print(","); Serial.print(yCell);
  Serial.print(") head="); Serial.print(heading);
  Serial.print("  F/L/R="); Serial.print(lastFrontMM); Serial.print("/");
  Serial.print(lastLeftMM); Serial.print("/"); Serial.print(lastRightMM);
  Serial.print("  FL/FR="); Serial.print(lastFLeftMM); Serial.print("/"); Serial.print(lastFRightMM);
  Serial.print("  traveled="); Serial.println(cellsTraveled);
}
