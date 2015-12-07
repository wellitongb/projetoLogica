
package cpu;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * Classe responsável por criar o arquivo LOG1.log e imprimir as informações de cada processo nele.
 * @author wellitongb
 */
public class CriarLog1 {
    private /*@ spec_public @*/ final File diretorio = new File("."); 
    private /*@ spec_public nullable @*/ FileWriter arquivo;
    private /*@ spec_public nullable @*/ PrintWriter output;
    
    /*@ public invariant arquivo != null
     @ && diretorio.exists();
     @*/
    
    /*@ public invariant output != null
    @ && arquivo != null
    @ && diretorio.exists();
    @*/
    
    
    /**
     *Método construtor da classe CriarLog1.
     * @param typeLog Representa o nome do algoritmo usado para criar o log.
     */
    /*@ requires typeLog != null;
     @ 	assignable this.arquivo;
     @	assignable this.output;
     @	ensures this.arquivo != null;
     @	ensures this.output != null;
     @*/
    public CriarLog1(String typeLog){
        openFile(typeLog);
        this.output.println("/*********************************");
        this.output.println("* Componentes do Grupo: ");
        this.output.println("* ELISIO BRENO GARCIA CARDOSO");
        this.output.println("* JOSÉ WELLITON NUNES JUNIOR");
        this.output.println("* MOISÉS CAVALCANTE FERNANDES");
        this.output.println("* VICTOR SANTIAGO VALENTE");
        this.output.println("**********************************/");
    }
    
    /*@ private normal_behavior
     @	requires typeLog != null;
     @ 	assignable this.arquivo;
     @	assignable this.output;
     @	ensures this.arquivo != null;
     @	ensures this.output != null;
     @*/
    private void openFile(String typeLog){ 
        try{
            this.arquivo = new FileWriter(this.diretorio.getAbsolutePath().substring(0, this.diretorio.getAbsolutePath().length() - 1).concat(typeLog + " - LOG1.log"));
            this.output = new PrintWriter(this.arquivo);
        }
        catch (IOException ex) {
            System.out.println("Erro ao criar arquivo");
            Logger.getLogger(CriarLog1.class.getName()).log(Level.SEVERE, null, ex);
        }   
    }
    
    /*@	requires this.output != null;
     @ assignable \nothing;
     @*/
    public /*@ pure @*/ void close(){
        this.output.close();
    }
    /**
     * Método que imprimi as informações do processo exigidas para o primeiro LOG.
     * @param process Representa o processo que será impresso as informações.
     * @param timeSystem Representa o tempo do sistema.
     * @throws Error Caso o processo não esteja no estado FINALIZADO.
     */
    /*@ requires process != null && process.getEstado() == 4;
     @	requires timeSystem > 0;
     @	assignable \nothing;
     @*/
    public void print(Processo process, int timeSystem){
        if(process.getEstado() == Processo.FINALIZADO){
            this.output.print(process.getPID() + " ");
            this.output.print(process.getTempoDeChegada() + " ");
            this.output.print(timeSystem + " ");
            this.output.print(process.getTimeExecutionGeral() + " ");
            this.output.print(process.getIOserviceTime() + " ");
            this.output.println(process.getLifeTime());
        }
        else{
            throw new Error("Processo nÃ£o foi FINALIZADO");
        }
    }
}
