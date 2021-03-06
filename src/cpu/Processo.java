package cpu;

/**
 * @author Jose Welliton Nunes Junior
 */
public class Processo {
    public static final int NOVO = 0;
    public static final int PRONTO = 1;
    public static final int EXECUTANDO = 2;
    public static final int ESPERA = 3;
    public static final int FINALIZADO = 4;
    private /*@ spec_public @*/ int PID = 0,tempoDeChegada = 0, estado = 0, lifeTime = 0, nPicos = 0, picoAtualIndex = 0,picoAtualValue = 0, IOserviceTime = 0, aux = 0;
    private /*@ spec_public nullable @*/ int[] picos;
    
    //@ public invariant 0 <= aux;
    //@ public invariant 0 <= 0; 
    //@ public invariant 0 <= PID; 
    //@ public invariant 0 <= tempoDeChegada;
    //@ public invariant 0 <= estado;
    //@ public invariant 0 <= lifeTime;
    //@ public invariant 0 <= nPicos;
    //@ public invariant 0 <= picoAtualIndex;
    //@ public invariant 0 <= picoAtualValue;
    //@ public invariant 0 <= IOserviceTime;
    /*@ public invariant picos != null
     @	&& (\forall int i; 0 <= i && i < picos.length;
     @ 			picos[i] >= 0);
     @*/
    
 
    /**
     * Metodo Contrutor da Classe Processo.
     * @param PID Par�metro que representa o ID do processo.
     * @param tempoDeChegada Par�metro que representa o tempo de Chegada do Processo.
     * @param nPicos Par�metro que representa o numero picos de tempo para processamento.
     */
    /*@ requires 0 <= PID && 0 <= tempoDeChegada && 0 <= nPicos;
    @	assignable this.PID;
    @	assignable this.tempoDeChegada;
    @	assignable this.nPicos;
    @	assignable this.picos;
    @	ensures picos.length == nPicos;
    @	ensures this.nPicos == nPicos;
    @   ensures this.tempoDeChegada == tempoDeChegada;
    @   ensures this.PID == PID;
    @*/ 
    public Processo(int PID,int tempoDeChegada, int nPicos) {
        this.PID = PID;
        this.tempoDeChegada = tempoDeChegada;
        this.nPicos = nPicos;
        this.picos = new int[nPicos];      
    }

    /**
     * Metodo set para a variavel estado.
     * @param estado
     */
    /*@ requires 0 <= estado && estado < 5;
     @ assignable this.estado;
     @ ensures this.estado == estado;
     @*/
    public void setEstado(int estado) {
        this.estado = estado;
    }
    
    /**
     * Metodo set para modificar o valor do pico atual, caso precise.
     * @param pico Par�metro que representa valor do pico.
     */
    /*@ requires 0 <= pico;
     @  assignable this.picoAtualValue;
     @	ensures this.picoAtualValue == pico;
     @*/
    public void setPicoAtualValue(int pico){
        this.picoAtualValue = pico;
    }

    /**
     * Metodo set para modificar o valor de qualquer pico, caso precise.
     * @param index Par�metro que representa o indice do pico.
     * @param pico Par�metro que representa o valor do pico.
     */
    /*@ requires 0 <= pico && 0 <= index && this.picos != null && this.picos.length >= index;
   	 @	assignable this.picos[index]; 
     @	ensures this.picos[index] == pico;
     @*/
    public void setPico(int index, int pico){
        this.picos[index] = pico;
    }

    /**
     * Metodo que incrementa o valor da variavel LifeTime em mais um.
     */
    /*@ requires 0 <= this.lifeTime;
  	 @	assignable this.lifeTime;
     @	ensures this.lifeTime == \old(lifeTime + 1);
     @*/
    public void addLifeTime() {
        this.lifeTime++;
    }

    /**
     * Metodo que incrementa o valor da variavel IOServiceTime em mais um.
     */
    /*@ requires 0 <= this.IOserviceTime;
 	 @	assignable this.IOserviceTime;
     @	ensures this.IOserviceTime == \old(IOserviceTime + 1);
     @*/
    public void addIOserviceTime() {
        this.IOserviceTime++;
    }
       
    /**
     * Metodo que incrementa o valor do indice do vetor de picos.
     */
    /*@ 	requires 0 <= this.nPicos && this.picoAtualIndex < this.nPicos;
	 @		assignable this.picoAtualIndex;
     @		ensures this.picoAtualIndex == \old(picoAtualIndex + 1);
     @	also
     @		requires this.picoAtualIndex == this.nPicos;
     @		assignable \nothing;
     @		ensures this.picoAtualIndex == \old(picoAtualIndex);
     @*/
    public void addPicoAtualIndex() {
        if(this.picoAtualIndex < this.nPicos){
            this.picoAtualIndex++;
            setPicoAtualValue(this.picos[picoAtualIndex]);
        }
    }
    
    /**
     * Metodo get para a variavel tempoDeChegada.
     * @return Retorna valor inteiro que representa o tempo de chegada.
     */
    //@ ensures \result == this.tempoDeChegada;
    public /*@ pure @*/ int getTempoDeChegada() {
        return tempoDeChegada;
    }
    
    /**
     * Metodo get para a variavel PID.
     * @return Retorna valor inteiro que representa o ID do processo.
     */
    //@ ensures \result == this.PID;
    public /*@ pure @*/ int getPID() {
        return this.PID;
    }

    /**
     * Metodo get da variavel IOServiceTime.
     * @return Retorna valor inteiro que representa o tempo de espera na fila de espera.
     */
    //@ ensures \result == this.IOserviceTime;
    public /*@ pure @*/ int getIOserviceTime() {
        return IOserviceTime;
    }
    
    /**
     * Metodo get da variavel Estado.  
     * @return Retorna valor inteiro que representa o estado atual do processo.
     */
    //@ ensures \result == this.estado;
    public /*@ pure @*/ int getEstado() {
        return this.estado;
    }

    /**
     * Metodo get da variavel picoAtualIndex.
     * @return Retorna um inteiro que representa a posicao, no vetor de picos, do pico atual.
     */
    //@ ensures \result == this.picoAtualIndex;
    public /*@ pure @*/ int getPicoAtualIndex() {
        return this.picoAtualIndex;
    }
    
    /**
     * Metodo get do valor do pico Atual.
     * @return Retorna um inteiro que representa o valor do pico atual.
     */
    //@ ensures \result == this.picoAtualValue;
    public /*@ pure @*/ int getPicoAtualValue(){
        return this.picoAtualValue;
    }
            
    /**
     * Metodo get da variavel LifeTime.
     * @return Retorna um inteiro que representa o valor do tempo de vida (tempo no sistema) do processo.
     */
    //@ ensures \result == this.lifeTime;
    public /*@ pure @*/ int getLifeTime() {
        return this.lifeTime;
    }

    /**
     * Metodo get da variavel nPicos.
     * @return Retorna um inteiro que representa o valor do numero de picos total desse processo.
     */
    //@ ensures \result == this.nPicos;
    public /*@ pure @*/ int getNPicos(){
        return this.nPicos;
    }
    
    /*@ requires 0 < this.picos.length;
     @  assignable this.aux;
     @	ensures aux > 0;
     @  ensures \result == aux;  
     @*/
    public int getTimeUseCPU(){ 
        this.aux = 0;        
        for(int i = 0; i < this.picos.length; i++){
            this.aux = this.aux + this.picos[i];
        }
        return this.aux;
    }
    
    /*@ 	requires this.estado == 4 && (0 < this.picos.length); 
     @  	ensures \result == this.aux + this.IOserviceTime;
     @	also
     @		requires this.estado != 4;
     @		ensures \result == -1;
     @*/	
    public int getTimeExecutionGeral(){
        if(this.estado == FINALIZADO){
            return this.IOserviceTime + getTimeUseCPU();
        }
        return -1;
    }
}
